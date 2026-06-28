#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>
#include <math.h>
#include <time.h>

#ifdef __EMSCRIPTEN__
#include <emscripten.h>
#else
#define EMSCRIPTEN_KEEPALIVE
#endif

#define MAX_ROWS 40
#define MAX_COLS 40
#define MAX_CELLS 1600
#define MAX_EDGES 3300
#define MAX_DOTS 1700

// Grid parameters
int rows = 0;
int cols = 0;
int numH = 0;
int numV = 0;
int numEdges = 0;
int numDots = 0;

// Core game buffers
int8_t edgeStates[MAX_EDGES]; // 0 = empty, 1 = line, -1 = cross
int8_t clues[MAX_CELLS];       // 0-3 cell clues, or -1 for null/empty

// Debug globals
static const char* dbgSource = "init";
static int lookaheadConfirmedCount = 0;
static int lookaheadMaxLimit = 0;
static bool isDoingLookahead = false;
static int dbgCell = -1;
static int dbgDot = -1;
static int8_t dbgTargetEdges[MAX_EDGES];
static bool hasDbgTarget = false;

// Generator variables
static int8_t genCells[MAX_ROWS][MAX_COLS];


// pre-allocated stack for backtracking search to avoid constant allocations
#define MAX_BACKTRACK_DEPTH 200
static int8_t backupStack[MAX_BACKTRACK_DEPTH][MAX_EDGES];
static int8_t backupAfterDeductStack[MAX_BACKTRACK_DEPTH][MAX_EDGES];


// Graph adjacency list arrays for loop connection tracing (avoids allocations)
static int adj[MAX_DOTS][4];
static int adjCount[MAX_DOTS];
static bool visitedDots[MAX_DOTS];

// BFS cell queue arrays
static int queueR[MAX_CELLS];
static int queueC[MAX_CELLS];
static bool visitedCells[MAX_ROWS][MAX_COLS];

// DSU (Disjoint Set Union) for fast cycle detection
static int dsuParent[MAX_DOTS];
static int dsuRank[MAX_DOTS];

typedef struct {
    int node;
    int parent;
    int rank;
} DSUSave;

static DSUSave dsuHistory[MAX_EDGES * 2];
static int dsuHistoryCount = 0;

static inline void dsuInit() {
    for (int i = 0; i < numDots; i++) {
        dsuParent[i] = i;
        dsuRank[i] = 0;
    }
    dsuHistoryCount = 0;
}

static inline int dsuFind(int i) {
    while (i != dsuParent[i]) {
        i = dsuParent[i];
    }
    return i;
}

static inline bool dsuUnion(int u, int v) {
    int rootU = dsuFind(u);
    int rootV = dsuFind(v);
    if (rootU == rootV) {
        return false; // Cycle detected!
    }
    dsuHistory[dsuHistoryCount++] = (DSUSave){ rootU, dsuParent[rootU], dsuRank[rootU] };
    dsuHistory[dsuHistoryCount++] = (DSUSave){ rootV, dsuParent[rootV], dsuRank[rootV] };
    
    if (dsuRank[rootU] < dsuRank[rootV]) {
        dsuParent[rootU] = rootV;
    } else if (dsuRank[rootU] > dsuRank[rootV]) {
        dsuParent[rootV] = rootU;
    } else {
        dsuParent[rootU] = rootV;
        dsuRank[rootV]++;
    }
    return true;
}

static inline void dsuInitFromCurrent() {
    dsuInit();
    for (int i = 0; i < numEdges; i++) {
        if (edgeStates[i] == 1) {
            int dotA, dotB;
            if (i < numH) {
                int r = i / cols;
                int c = i % cols;
                dotA = r * (cols + 1) + c;
                dotB = dotA + 1;
            } else {
                int vIdx = i - numH;
                int r = vIdx / (cols + 1);
                int c = vIdx % (cols + 1);
                dotA = r * (cols + 1) + c;
                dotB = dotA + (cols + 1);
            }
            dsuUnion(dotA, dotB);
        }
    }
}

static inline void dsuRollback(int checkpoint) {
    while (dsuHistoryCount > checkpoint) {
        DSUSave save = dsuHistory[--dsuHistoryCount];
        dsuParent[save.node] = save.parent;
        dsuRank[save.node] = save.rank;
    }
}

// AC-3 Dirty Queue arrays
static int cellQueue[MAX_CELLS * 4];
static int cellQueueHead = 0;
static int cellQueueTail = 0;
static bool cellInQueue[MAX_CELLS];

static int dotQueue[MAX_DOTS * 4];
static int dotQueueHead = 0;
static int dotQueueTail = 0;
static bool dotInQueue[MAX_DOTS];

static inline void enqueueCell(int r, int c) {
    if (r < 0 || r >= rows || c < 0 || c >= cols) return;
    int idx = r * cols + c;
    if (clues[idx] == -1) return; // Only process cells with clues
    if (!cellInQueue[idx]) {
        cellQueue[cellQueueTail++] = idx;
        if (cellQueueTail >= MAX_CELLS * 4) cellQueueTail = 0;
        cellInQueue[idx] = true;
    }
}

static inline int dequeueCell() {
    if (cellQueueHead == cellQueueTail) return -1;
    int idx = cellQueue[cellQueueHead++];
    if (cellQueueHead >= MAX_CELLS * 4) cellQueueHead = 0;
    cellInQueue[idx] = false;
    return idx;
}

static inline void enqueueDot(int r, int c) {
    if (r < 0 || r > rows || c < 0 || c > cols) return;
    int idx = r * (cols + 1) + c;
    if (!dotInQueue[idx]) {
        dotQueue[dotQueueTail++] = idx;
        if (dotQueueTail >= MAX_DOTS * 4) dotQueueTail = 0;
        dotInQueue[idx] = true;
    }
}

static inline int dequeueDot() {
    if (dotQueueHead == dotQueueTail) return -1;
    int idx = dotQueue[dotQueueHead++];
    if (dotQueueHead >= MAX_DOTS * 4) dotQueueHead = 0;
    dotInQueue[idx] = false;
    return idx;
}

// Forward declarations
static inline bool setEdgeState(int edgeIdx, int8_t state);
EMSCRIPTEN_KEEPALIVE bool isSolved();

// Candidate coords structure
typedef struct {
    int r;
    int c;
    double score;
} Candidate;

// API functions
EMSCRIPTEN_KEEPALIVE
void init_grid(int r, int c) {
    rows = r;
    cols = c;
    numH = (r + 1) * c;
    numV = r * (c + 1);
    numEdges = numH + numV;
    numDots = (r + 1) * (c + 1);
    memset(edgeStates, 0, sizeof(edgeStates));
    memset(clues, -1, sizeof(clues));
    edgeStates[numEdges] = -1; // Sentinel edge
}

EMSCRIPTEN_KEEPALIVE
int8_t* get_edge_states_ptr() {
    return edgeStates;
}

EMSCRIPTEN_KEEPALIVE
int8_t* get_clues_ptr() {
    return clues;
}

EMSCRIPTEN_KEEPALIVE
void set_random_seed(unsigned int seed) {
    srand(seed);
}

// Inline coordinate mappings
static inline int getClue(int r, int c) {
    if (r < 0 || r >= rows || c < 0 || c >= cols) return -1;
    return clues[r * cols + c];
}

static inline int getHEdgeIndex(int r, int c) {
    if (r < 0 || r > rows || c < 0 || c >= cols) return numEdges;
    return r * cols + c;
}

static inline int getVEdgeIndex(int r, int c) {
    if (r < 0 || r >= rows || c < 0 || c > cols) return numEdges;
    return numH + r * (cols + 1) + c;
}

static inline void getCellEdges(int r, int c, int* outEdges) {
    outEdges[0] = r * cols + c;                         // top
    outEdges[1] = numH + r * (cols + 1) + (c + 1);      // right
    outEdges[2] = (r + 1) * cols + c;                     // bottom
    outEdges[3] = numH + r * (cols + 1) + c;            // left
}

static inline int getDotEdges(int r, int c, int* outEdges) {
    outEdges[0] = getVEdgeIndex(r - 1, c);     // Up
    outEdges[1] = getVEdgeIndex(r, c);         // Down
    outEdges[2] = getHEdgeIndex(r, c - 1);     // Left
    outEdges[3] = getHEdgeIndex(r, c);         // Right
    return 4;
}

static inline bool setEdgeState(int edgeIdx, int8_t state) {
    if (edgeIdx == numEdges) return state == -1; // Sentinel edge must be cross
    if (edgeIdx < 0 || edgeIdx > numEdges) {
        printf("[C ERROR] setEdgeState out of bounds: %d (numEdges=%d)\n", edgeIdx, numEdges);
        return false;
    }
    if (edgeStates[edgeIdx] == state) return true; // Already set to this state
    if (edgeStates[edgeIdx] != 0) return false;    // Contradiction: edge is already determined to a different state
    
    // Lookahead limit check
    if (isDoingLookahead && lookaheadMaxLimit > 0 && lookaheadConfirmedCount >= lookaheadMaxLimit) {
        return true; // Limit reached: treat as success (no contradiction yet)
    }
    if (isDoingLookahead && lookaheadMaxLimit > 0) {
        lookaheadConfirmedCount++;
    }
    
    if (state == 1) {
        int dotA, dotB;
        if (edgeIdx < numH) {
            int r = edgeIdx / cols;
            int c = edgeIdx % cols;
            dotA = r * (cols + 1) + c;
            dotB = dotA + 1;
        } else {
            int vIdx = edgeIdx - numH;
            int r = vIdx / (cols + 1);
            int c = vIdx % (cols + 1);
            dotA = r * (cols + 1) + c;
            dotB = dotA + (cols + 1);
        }
        if (!dsuUnion(dotA, dotB)) {
            // Cycle closed! Check if it's a valid complete solved loop
            edgeStates[edgeIdx] = 1;
            bool solved = isSolved();
            edgeStates[edgeIdx] = 0;
            if (!solved) {
                return false; // Contradiction: Premature loop closed!
            }
        }
    }

    edgeStates[edgeIdx] = state;
    // Local queue propagation
    if (edgeIdx < numH) {
        int r = edgeIdx / cols;
        int c = edgeIdx % cols;
        enqueueCell(r - 1, c);
        enqueueCell(r, c);
        enqueueDot(r, c);
        enqueueDot(r, c + 1);
    } else {
        int vIdx = edgeIdx - numH;
        int r = vIdx / (cols + 1);
        int c = vIdx % (cols + 1);
        enqueueCell(r, c - 1);
        enqueueCell(r, c);
        enqueueDot(r, c);
        enqueueDot(r + 1, c);
    }
    
    return true;
}

// TRACE PREMATURE LOOPS (WASM optimized BFS cycle tracer)
bool preventsPrematureLoops() {
    memset(adjCount, 0, sizeof(adjCount));
    int totalDrawn = 0;

    for (int r = 0; r <= rows; r++) {
        for (int c = 0; c <= cols; c++) {
            int dotId = r * (cols + 1) + c;
            
            if (c < cols) {
                int hIdx = r * cols + c;
                if (edgeStates[hIdx] == 1) {
                    int neighborId = dotId + 1;
                    adj[dotId][adjCount[dotId]++] = neighborId;
                    adj[neighborId][adjCount[neighborId]++] = dotId;
                    totalDrawn++;
                }
            }
            if (r < rows) {
                int vIdx = numH + r * (cols + 1) + c;
                if (edgeStates[vIdx] == 1) {
                    int neighborId = dotId + (cols + 1);
                    adj[dotId][adjCount[dotId]++] = neighborId;
                    adj[neighborId][adjCount[neighborId]++] = dotId;
                    totalDrawn++;
                }
            }
        }
    }

    totalDrawn /= 2;
    if (totalDrawn == 0) return true;

    memset(visitedDots, 0, sizeof(visitedDots));
    int loopsCount = 0;
    int loopDotCount = 0;
    int visitedCount = 0;

    for (int i = 0; i < numDots; i++) {
        if (adjCount[i] > 0 && !visitedDots[i]) {
            int curr = i;
            int prev = -1;
            bool isLoop = true;
            int componentSize = 0;

            while (true) {
                visitedDots[curr] = true;
                visitedCount++;
                componentSize++;

                int next = -1;
                for (int j = 0; j < adjCount[curr]; j++) {
                    int n = adj[curr][j];
                    if (n != prev) {
                        next = n;
                        break;
                    }
                }

                if (next == -1) {
                    isLoop = false;
                    break;
                }

                if (visitedDots[next]) {
                    if (next != i) {
                        isLoop = false;
                    }
                    break;
                }

                prev = curr;
                curr = next;
            }

            if (isLoop && componentSize > 2) {
                loopsCount++;
                loopDotCount += componentSize;
            }
        }
    }

    if (loopsCount > 0) {
        if (loopsCount > 1 || loopDotCount < visitedCount) {
            return false; // Multiple loops or disconnected paths
        }

        // Single closed loop, verify if any undecided edges exist
        bool hasUndecided = false;
        for (int i = 0; i < numEdges; i++) {
            if (edgeStates[i] == 0) {
                hasUndecided = true;
                break;
            }
        }

        // Allow normal backtracking exploration to proceed to leaf nodes.
    }

    return true;
}

// AC-3 Queue Utility to reset state on backtrack rollback
static inline void clearQueues() {
    cellQueueHead = 0;
    cellQueueTail = 0;
    memset(cellInQueue, 0, sizeof(cellInQueue));
    
    dotQueueHead = 0;
    dotQueueTail = 0;
    memset(dotInQueue, 0, sizeof(dotInQueue));
}

static bool applyStaticRules() {
    dbgSource = "static_rules";

    for (int r = 0; r < rows; r++) {
        for (int c = 0; c < cols; c++) {
            int clue = clues[r * cols + c];
            if (clue == -1) continue;
            
            // Rule 2.1: Orthogonally Adjacent 3-3 Cells
            if (clue == 3) {
                if (c + 1 < cols && clues[r * cols + (c + 1)] == 3) {
                    int shared = getVEdgeIndex(r, c + 1);
                    int outerL = getVEdgeIndex(r, c);
                    int outerR = getVEdgeIndex(r, c + 2);
                    if (!setEdgeState(shared, 1)) return false;
                    if (!setEdgeState(outerL, 1)) return false;
                    if (!setEdgeState(outerR, 1)) return false;
                }
                if (r + 1 < rows && clues[(r + 1) * cols + c] == 3) {
                    int shared = getHEdgeIndex(r + 1, c);
                    int outerT = getHEdgeIndex(r, c);
                    int outerB = getHEdgeIndex(r + 2, c);
                    if (!setEdgeState(shared, 1)) return false;
                    if (!setEdgeState(outerT, 1)) return false;
                    if (!setEdgeState(outerB, 1)) return false;
                }
            }
            
            // Rule 2.2: Diagonally Adjacent 3-3 Cells
            if (clue == 3) {
                if (r + 1 < rows && c + 1 < cols && clues[(r + 1) * cols + (c + 1)] == 3) {
                    int tA = getHEdgeIndex(r, c);
                    int lA = getVEdgeIndex(r, c);
                    int bB = getHEdgeIndex(r + 2, c + 1);
                    int rB = getVEdgeIndex(r + 1, c + 2);
                    if (!setEdgeState(tA, 1)) return false;
                    if (!setEdgeState(lA, 1)) return false;
                    if (!setEdgeState(bB, 1)) return false;
                    if (!setEdgeState(rB, 1)) return false;
                }
                if (r + 1 < rows && c - 1 >= 0 && clues[(r + 1) * cols + (c - 1)] == 3) {
                    int tA = getHEdgeIndex(r, c);
                    int rA = getVEdgeIndex(r, c + 1);
                    int bB = getHEdgeIndex(r + 2, c - 1);
                    int lB = getVEdgeIndex(r + 1, c - 1);
                    if (!setEdgeState(tA, 1)) return false;
                    if (!setEdgeState(rA, 1)) return false;
                    if (!setEdgeState(bB, 1)) return false;
                    if (!setEdgeState(lB, 1)) return false;
                }
            }
            
            // Rule 2.3: 0-3 Orthogonal Adjacency
            if (clue == 0) {
                int dr[] = {-1, 1, 0, 0};
                int dc[] = {0, 0, -1, 1};
                for (int dir = 0; dir < 4; dir++) {
                    int nr = r + dr[dir];
                    int nc = c + dc[dir];
                    if (nr >= 0 && nr < rows && nc >= 0 && nc < cols) {
                        if (clues[nr * cols + nc] == 3) {
                            int t3 = getHEdgeIndex(nr, nc);
                            int r3 = getVEdgeIndex(nr, nc + 1);
                            int b3 = getHEdgeIndex(nr + 1, nc);
                            int l3 = getVEdgeIndex(nr, nc);
                            
                            if (dir == 0) {
                                if (!setEdgeState(t3, 1)) return false;
                                if (!setEdgeState(r3, 1)) return false;
                                if (!setEdgeState(l3, 1)) return false;
                            } else if (dir == 1) {
                                if (!setEdgeState(b3, 1)) return false;
                                if (!setEdgeState(r3, 1)) return false;
                                if (!setEdgeState(l3, 1)) return false;
                            } else if (dir == 2) {
                                if (!setEdgeState(t3, 1)) return false;
                                if (!setEdgeState(b3, 1)) return false;
                                if (!setEdgeState(l3, 1)) return false;
                            } else if (dir == 3) {
                                if (!setEdgeState(t3, 1)) return false;
                                if (!setEdgeState(b3, 1)) return false;
                                if (!setEdgeState(r3, 1)) return false;
                            }
                        }
                    }
                }
            }
            
            // Rule 2.5: Diagonally Adjacent 0-3 and 0-1 Cells
            if (clue == 0) {
                // Bottom-Right
                if (r + 1 < rows && c + 1 < cols) {
                    int diagClue = clues[(r + 1) * cols + (c + 1)];
                    if (diagClue == 3 || diagClue == 1) {
                        int tA = getHEdgeIndex(r + 1, c + 1);
                        int lA = getVEdgeIndex(r + 1, c + 1);
                        int state = (diagClue == 3) ? 1 : -1;
                        if (!setEdgeState(tA, state)) return false;
                        if (!setEdgeState(lA, state)) return false;
                    }
                }
                // Bottom-Left
                if (r + 1 < rows && c - 1 >= 0) {
                    int diagClue = clues[(r + 1) * cols + (c - 1)];
                    if (diagClue == 3 || diagClue == 1) {
                        int tB = getHEdgeIndex(r + 1, c - 1);
                        int rB = getVEdgeIndex(r + 1, c);
                        int state = (diagClue == 3) ? 1 : -1;
                        if (!setEdgeState(tB, state)) return false;
                        if (!setEdgeState(rB, state)) return false;
                    }
                }
                // Top-Right
                if (r - 1 >= 0 && c + 1 < cols) {
                    int diagClue = clues[(r - 1) * cols + (c + 1)];
                    if (diagClue == 3 || diagClue == 1) {
                        int bC = getHEdgeIndex(r, c + 1);
                        int lC = getVEdgeIndex(r - 1, c + 1);
                        int state = (diagClue == 3) ? 1 : -1;
                        if (!setEdgeState(bC, state)) return false;
                        if (!setEdgeState(lC, state)) return false;
                    }
                }
                // Top-Left
                if (r - 1 >= 0 && c - 1 >= 0) {
                    int diagClue = clues[(r - 1) * cols + (c - 1)];
                    if (diagClue == 3 || diagClue == 1) {
                        int bD = getHEdgeIndex(r, c - 1);
                        int rD = getVEdgeIndex(r - 1, c);
                        int state = (diagClue == 3) ? 1 : -1;
                        if (!setEdgeState(bD, state)) return false;
                        if (!setEdgeState(rD, state)) return false;
                    }
                }
            }
        }
    }
    return true;
}

static inline bool areEdgesForcedEqual(int e1, int e2, int dotR, int dotC) {
    if (edgeStates[e1] != 0 && edgeStates[e2] != 0 && edgeStates[e1] == edgeStates[e2]) return true;
    int dotEdges[4];
    int count = getDotEdges(dotR, dotC, dotEdges);
    int lines = 0, undecidedCount = 0;
    bool containsE1 = false, containsE2 = false;
    for (int i = 0; i < count; i++) {
        int e = dotEdges[i];
        if (edgeStates[e] == 1) lines++;
        else if (edgeStates[e] == 0) undecidedCount++;
        if (e == e1) containsE1 = true;
        if (e == e2) containsE2 = true;
    }
    if (containsE1 && containsE2 && lines == 0 && undecidedCount == 2 && edgeStates[e1] == 0 && edgeStates[e2] == 0) {
        return true;
    }
    return false;
}

static bool applyAdvanced2Rules() {
    for (int r = 0; r < rows; r++) {
        for (int c = 0; c < cols; c++) {
            if (clues[r * cols + c] == 2) {
                int eT = getHEdgeIndex(r, c);
                int eB = getHEdgeIndex(r + 1, c);
                int eL = getVEdgeIndex(r, c);
                int eR = getVEdgeIndex(r, c + 1);
                
                if (areEdgesForcedEqual(eT, eL, r, c)) {
                    if (edgeStates[eB] != 0 && edgeStates[eR] == 0) { if (!setEdgeState(eR, edgeStates[eB])) return false; }
                    else if (edgeStates[eR] != 0 && edgeStates[eB] == 0) { if (!setEdgeState(eB, edgeStates[eR])) return false; }
                    else if (edgeStates[eB] != 0 && edgeStates[eR] != 0 && edgeStates[eB] != edgeStates[eR]) return false;
                }
                if (areEdgesForcedEqual(eT, eR, r, c + 1)) {
                    if (edgeStates[eB] != 0 && edgeStates[eL] == 0) { if (!setEdgeState(eL, edgeStates[eB])) return false; }
                    else if (edgeStates[eL] != 0 && edgeStates[eB] == 0) { if (!setEdgeState(eB, edgeStates[eL])) return false; }
                    else if (edgeStates[eB] != 0 && edgeStates[eL] != 0 && edgeStates[eB] != edgeStates[eL]) return false;
                }
                if (areEdgesForcedEqual(eB, eL, r + 1, c)) {
                    if (edgeStates[eT] != 0 && edgeStates[eR] == 0) { if (!setEdgeState(eR, edgeStates[eT])) return false; }
                    else if (edgeStates[eR] != 0 && edgeStates[eT] == 0) { if (!setEdgeState(eT, edgeStates[eR])) return false; }
                    else if (edgeStates[eT] != 0 && edgeStates[eR] != 0 && edgeStates[eT] != edgeStates[eR]) return false;
                }
                if (areEdgesForcedEqual(eB, eR, r + 1, c + 1)) {
                    if (edgeStates[eT] != 0 && edgeStates[eL] == 0) { if (!setEdgeState(eL, edgeStates[eT])) return false; }
                    else if (edgeStates[eL] != 0 && edgeStates[eT] == 0) { if (!setEdgeState(eT, edgeStates[eL])) return false; }
                    else if (edgeStates[eT] != 0 && edgeStates[eL] != 0 && edgeStates[eT] != edgeStates[eL]) return false;
                }
            }
        }
    }
    return true;
}

static inline bool deductParityPair(int e1, int e2, int e3, int e4) {
    int8_t s1 = (e1 == -1) ? -1 : edgeStates[e1];
    int8_t s2 = (e2 == -1) ? -1 : edgeStates[e2];
    int8_t s3 = (e3 == -1) ? -1 : edgeStates[e3];
    int8_t s4 = (e4 == -1) ? -1 : edgeStates[e4];
    
    int undecidedCount = 0;
    if (s1 == 0) undecidedCount++;
    if (s2 == 0) undecidedCount++;
    if (s3 == 0) undecidedCount++;
    if (s4 == 0) undecidedCount++;
    
    if (undecidedCount == 1) {
        int v1 = (s1 == 1) ? 1 : 0;
        int v2 = (s2 == 1) ? 1 : 0;
        int v3 = (s3 == 1) ? 1 : 0;
        int v4 = (s4 == 1) ? 1 : 0;
        
        if (s1 == 0) {
            int target = (v3 + v4 - v2 + 2) % 2;
            if (!setEdgeState(e1, target == 1 ? 1 : -1)) return false;
        } else if (s2 == 0) {
            int target = (v3 + v4 - v1 + 2) % 2;
            if (!setEdgeState(e2, target == 1 ? 1 : -1)) return false;
        } else if (s3 == 0) {
            int target = (v1 + v2 - v4 + 2) % 2;
            if (!setEdgeState(e3, target == 1 ? 1 : -1)) return false;
        } else if (s4 == 0) {
            int target = (v1 + v2 - v3 + 2) % 2;
            if (!setEdgeState(e4, target == 1 ? 1 : -1)) return false;
        }
    } else if (undecidedCount == 0) {
        int v1 = (s1 == 1) ? 1 : 0;
        int v2 = (s2 == 1) ? 1 : 0;
        int v3 = (s3 == 1) ? 1 : 0;
        int v4 = (s4 == 1) ? 1 : 0;
        if ((v1 + v2) % 2 != (v3 + v4) % 2) {
            return false;
        }
    }
    return true;
}

static inline bool deductCutParity(const int* cutEdges, int cutSize) {
    int undecidedCount = 0;
    int undecidedIdx = -1;
    int lineCount = 0;
    for (int i = 0; i < cutSize; i++) {
        int e = cutEdges[i];
        if (e == -1) continue;
        if (edgeStates[e] == 1) {
            lineCount++;
        } else if (edgeStates[e] == 0) {
            undecidedCount++;
            undecidedIdx = e;
        }
    }
    
    if (undecidedCount == 1) {
        int target = (lineCount % 2 == 1) ? 1 : -1;
        if (!setEdgeState(undecidedIdx, target)) {
            return false;
        }
    } else if (undecidedCount == 0) {
        if (lineCount % 2 != 0) {
            return false;
        }
    }
    return true;
}

static bool deductJordanCurveParity() {
    int maxK = rows < cols ? rows : cols;
    static int cutEdges[100];
    for (int k = 1; k <= maxK; k++) {
        // Top-Left
        int count = 0;
        for (int r = 0; r < k; r++) {
            int h = getHEdgeIndex(r, k - 1 - r);
            if (h != -1) cutEdges[count++] = h;
        }
        for (int c = 0; c < k; c++) {
            int v = getVEdgeIndex(k - 1 - c, c);
            if (v != -1) cutEdges[count++] = v;
        }
        if (count > 0) {
            if (!deductCutParity(cutEdges, count)) return false;
        }
        
        // Top-Right
        count = 0;
        for (int r = 0; r < k; r++) {
            int h = getHEdgeIndex(r, cols - k + r);
            if (h != -1) cutEdges[count++] = h;
        }
        for (int c = 0; c < k; c++) {
            int v = getVEdgeIndex(k - 1 - c, cols - c);
            if (v != -1) cutEdges[count++] = v;
        }
        if (count > 0) {
            if (!deductCutParity(cutEdges, count)) return false;
        }
        
        // Bottom-Left
        count = 0;
        for (int c = 0; c < k; c++) {
            int h = getHEdgeIndex(rows - k + 1 + c, c);
            if (h != -1) cutEdges[count++] = h;
        }
        for (int r = 0; r < k; r++) {
            int v = getVEdgeIndex(rows - k + r, r);
            if (v != -1) cutEdges[count++] = v;
        }
        if (count > 0) {
            if (!deductCutParity(cutEdges, count)) return false;
        }
        
        // Bottom-Right
        count = 0;
        for (int i = 0; i < k; i++) {
            int h = getHEdgeIndex(rows - i, cols - k + i);
            if (h != -1) cutEdges[count++] = h;
        }
        for (int i = 0; i < k; i++) {
            int v = getVEdgeIndex(rows - k + i, cols - i);
            if (v != -1) cutEdges[count++] = v;
        }
        if (count > 0) {
            if (!deductCutParity(cutEdges, count)) return false;
        }
    }
    return true;
}

// LOGICAL DEDUCTION ENGINE - INCREMENTAL PASS (AC-3 local constraint propagation)
static bool propagateDiagonal2s(int startR, int startC, int dr, int dc) {
    int curr_r = startR;
    int curr_c = startC;
    while (getClue(curr_r, curr_c) == 2) {
        curr_r += dr;
        curr_c += dc;
    }
    int clue = getClue(curr_r, curr_c);
    if (clue != -1) {
        
        int oppEdge1 = -1, oppEdge2 = -1;
        if (dr == 1 && dc == 1) { 
            oppEdge1 = getHEdgeIndex(curr_r + 1, curr_c);
            oppEdge2 = getVEdgeIndex(curr_r, curr_c + 1);
        } else if (dr == -1 && dc == -1) { 
            oppEdge1 = getHEdgeIndex(curr_r, curr_c);
            oppEdge2 = getVEdgeIndex(curr_r, curr_c);
        } else if (dr == -1 && dc == 1) { 
            oppEdge1 = getHEdgeIndex(curr_r, curr_c);
            oppEdge2 = getVEdgeIndex(curr_r, curr_c + 1);
        } else if (dr == 1 && dc == -1) { 
            oppEdge1 = getHEdgeIndex(curr_r + 1, curr_c);
            oppEdge2 = getVEdgeIndex(curr_r, curr_c);
        }
        
        if (clue == 0) return false;
        else if (clue == 1) {
            if (!setEdgeState(oppEdge1, -1)) return false;
            if (!setEdgeState(oppEdge2, -1)) return false;
        } else if (clue == 3) {
            if (!setEdgeState(oppEdge1, 1)) return false;
            if (!setEdgeState(oppEdge2, 1)) return false;
        }
    }
    return true;
}

// Returns true if assuming cell (r,c) passes 0 lines to dot in direction (dr, dc) causes a contradiction.
static inline bool checkZeroLineAssumption(int r, int c, int dr, int dc) {
    int curr_r = r + dr;
    int curr_c = c + dc;
    while (getClue(curr_r, curr_c) == 2) {
        curr_r += dr;
        curr_c += dc;
    }
    int clue = getClue(curr_r, curr_c);
    if (clue == -1) return false; // Boundary is fine with 0 lines
    if (clue == 0) return false;  // 0 cell is fine with 0 lines (2 crosses)
    if (clue == 3) return true;   // 3 cell CANNOT have 2 crosses! Contradiction!
    
    // Find opposite edges of the end cell
    int oppEdge1, oppEdge2;
    if (dr == 1 && dc == 1) { 
        oppEdge1 = getHEdgeIndex(curr_r + 1, curr_c);
        oppEdge2 = getVEdgeIndex(curr_r, curr_c + 1);
    } else if (dr == -1 && dc == -1) { 
        oppEdge1 = getHEdgeIndex(curr_r, curr_c);
        oppEdge2 = getVEdgeIndex(curr_r, curr_c);
    } else if (dr == -1 && dc == 1) { 
        oppEdge1 = getHEdgeIndex(curr_r, curr_c);
        oppEdge2 = getVEdgeIndex(curr_r, curr_c + 1);
    } else if (dr == 1 && dc == -1) { 
        oppEdge1 = getHEdgeIndex(curr_r + 1, curr_c);
        oppEdge2 = getVEdgeIndex(curr_r, curr_c);
    }
    
    if (clue == 2) {
        // 2 cell needs 2 lines. Incoming is 0 lines (2 crosses).
        // So opposite edges MUST both be 1.
        if (edgeStates[oppEdge1] == -1 || edgeStates[oppEdge2] == -1) return true;
    } else if (clue == 1) {
        // 1 cell needs 1 line. Incoming is 0 lines.
        // So opposite edges MUST be {1, -1}.
        if (edgeStates[oppEdge1] == -1 && edgeStates[oppEdge2] == -1) return true;
    }
    return false;
}

static inline bool deductIncremental() {
    int loopCount = 0;
    while (true) {
        loopCount++;
        if (loopCount > 10000) {
            printf("[C ERROR] deductIncremental infinite loop detected! queue sizes: cells=%d, dots=%d\n", 
                   (cellQueueTail - cellQueueHead + MAX_CELLS * 4) % (MAX_CELLS * 4),
                   (dotQueueTail - dotQueueHead + MAX_DOTS * 4) % (MAX_DOTS * 4));
            return false; // Force stop
        }
        while (cellQueueHead != cellQueueTail || dotQueueHead != dotQueueTail) {
            // 1. Process cells
            int cellIdx = dequeueCell();
            if (cellIdx != -1) {
                dbgSource = "cell";
                dbgCell = cellIdx;
                dbgDot = -1;
                int r = cellIdx / cols;
                int c = cellIdx % cols;
                int clue = clues[cellIdx];
                if (clue != -1) {
                    int cellEdges[4];
                    getCellEdges(r, c, cellEdges);
                    int lines = 0;
                    int crosses = 0;
                    int undecided[4];
                    int undecidedCount = 0;
                    
                    for (int j = 0; j < 4; j++) {
                        int idx = cellEdges[j];
                        if (edgeStates[idx] == 1) lines++;
                        else if (edgeStates[idx] == -1) crosses++;
                        else undecided[undecidedCount++] = idx;
                    }
                    
                    if (lines > clue || crosses > (4 - clue)) {
                        return false; // Contradiction
                    }
                    
                    if (undecidedCount > 0) {
                        if (lines == clue) {
                            for (int j = 0; j < undecidedCount; j++) {
                                if (!setEdgeState(undecided[j], -1)) {
                                    return false;
                                }
                            }
                        } else if (crosses == (4 - clue)) {
                            for (int j = 0; j < undecidedCount; j++) {
                                if (!setEdgeState(undecided[j], 1)) {
                                    return false;
                                }
                            }
                        }
                    }
                    
                    if (clue == 3) {
                        int eT = cellEdges[0];
                        int eR = cellEdges[1];
                        int eB = cellEdges[2];
                        int eL = cellEdges[3];
                        // Early SLE for Clue 3
                        if (edgeStates[eT] == 1 && edgeStates[eL] == 1) { if (!propagateDiagonal2s(r + 1, c + 1, 1, 1)) return false; }
                        if (edgeStates[eT] == 1 && edgeStates[eR] == 1) { if (!propagateDiagonal2s(r + 1, c - 1, 1, -1)) return false; }
                        if (edgeStates[eB] == 1 && edgeStates[eL] == 1) { if (!propagateDiagonal2s(r - 1, c + 1, -1, 1)) return false; }
                        if (edgeStates[eB] == 1 && edgeStates[eR] == 1) { if (!propagateDiagonal2s(r - 1, c - 1, -1, -1)) return false; }
                        
                        // Down-Right dot is eB, eR. Opposite is eT, eL.
                        if (checkZeroLineAssumption(r, c, 1, 1)) {
                            if (!setEdgeState(eT, 1)) return false;
                            if (!setEdgeState(eL, 1)) return false;
                        }
                        // Down-Left dot is eB, eL. Opposite is eT, eR.
                        if (checkZeroLineAssumption(r, c, 1, -1)) {
                            if (!setEdgeState(eT, 1)) return false;
                            if (!setEdgeState(eR, 1)) return false;
                        }
                        // Up-Right dot is eT, eR. Opposite is eB, eL.
                        if (checkZeroLineAssumption(r, c, -1, 1)) {
                            if (!setEdgeState(eB, 1)) return false;
                            if (!setEdgeState(eL, 1)) return false;
                        }
                        // Up-Left dot is eT, eL. Opposite is eB, eR.
                        if (checkZeroLineAssumption(r, c, -1, -1)) {
                            if (!setEdgeState(eB, 1)) return false;
                            if (!setEdgeState(eR, 1)) return false;
                        }

                    } else if (clue == 1) {
                        int eT = cellEdges[0];
                        int eR = cellEdges[1];
                        int eB = cellEdges[2];
                        int eL = cellEdges[3];
                        // Early SLE for Clue 1
                        if (edgeStates[eT] == -1 && edgeStates[eL] == -1) { if (!propagateDiagonal2s(r + 1, c + 1, 1, 1)) return false; }
                        if (edgeStates[eT] == -1 && edgeStates[eR] == -1) { if (!propagateDiagonal2s(r + 1, c - 1, 1, -1)) return false; }
                        if (edgeStates[eB] == -1 && edgeStates[eL] == -1) { if (!propagateDiagonal2s(r - 1, c + 1, -1, 1)) return false; }
                        if (edgeStates[eB] == -1 && edgeStates[eR] == -1) { if (!propagateDiagonal2s(r - 1, c - 1, -1, -1)) return false; }

                    } else if (clue == 2) {
                        int eT = cellEdges[0];
                        int eR = cellEdges[1];
                        int eB = cellEdges[2];
                        int eL = cellEdges[3];
                        // Early SLE for Clue 2 (User's observation)
                        // Top-Left Dot Outside Edges: H(r, c-1) and V(r-1, c)
                        int outT_L = getHEdgeIndex(r, c - 1);
                        int outL_T = getVEdgeIndex(r - 1, c);
                        if (outT_L != -1 && outL_T != -1 && edgeStates[outT_L] != 0 && edgeStates[outT_L] == edgeStates[outL_T]) {
                            if (!propagateDiagonal2s(r - 1, c + 1, -1, 1)) return false; // Up-Right
                            if (!propagateDiagonal2s(r + 1, c - 1, 1, -1)) return false; // Down-Left
                        }
                        // Top-Right Dot Outside Edges: H(r, c+1) and V(r-1, c+1)
                        int outT_R = getHEdgeIndex(r, c + 1);
                        int outR_T = getVEdgeIndex(r - 1, c + 1);
                        if (outT_R != -1 && outR_T != -1 && edgeStates[outT_R] != 0 && edgeStates[outT_R] == edgeStates[outR_T]) {
                            if (!propagateDiagonal2s(r - 1, c - 1, -1, -1)) return false; // Up-Left
                            if (!propagateDiagonal2s(r + 1, c + 1, 1, 1)) return false;   // Down-Right
                        }
                        // Bottom-Left Dot Outside Edges: H(r+1, c-1) and V(r+1, c)
                        int outB_L = getHEdgeIndex(r + 1, c - 1);
                        int outL_B = getVEdgeIndex(r + 1, c);
                        if (outB_L != -1 && outL_B != -1 && edgeStates[outB_L] != 0 && edgeStates[outB_L] == edgeStates[outL_B]) {
                            if (!propagateDiagonal2s(r - 1, c - 1, -1, -1)) return false; // Up-Left
                            if (!propagateDiagonal2s(r + 1, c + 1, 1, 1)) return false;   // Down-Right
                        }
                        // Bottom-Right Dot Outside Edges: H(r+1, c+1) and V(r+1, c+1)
                        int outB_R = getHEdgeIndex(r + 1, c + 1);
                        int outR_B = getVEdgeIndex(r + 1, c + 1);
                        if (outB_R != -1 && outR_B != -1 && edgeStates[outB_R] != 0 && edgeStates[outB_R] == edgeStates[outR_B]) {
                            if (!propagateDiagonal2s(r - 1, c + 1, -1, 1)) return false; // Up-Right
                            if (!propagateDiagonal2s(r + 1, c - 1, 1, -1)) return false; // Down-Left
                        }
                        
                        // Down-Right dot is eB, eR. Opposite is eT, eL.
                        if (checkZeroLineAssumption(r, c, 1, 1)) {
                            // Opposite edges CANNOT both be -1.
                            if (edgeStates[eT] == -1 && edgeStates[eL] == 0) { if (!setEdgeState(eL, 1)) return false; }
                            if (edgeStates[eL] == -1 && edgeStates[eT] == 0) { if (!setEdgeState(eT, 1)) return false; }
                        }
                        // Down-Left dot is eB, eL. Opposite is eT, eR.
                        if (checkZeroLineAssumption(r, c, 1, -1)) {
                            if (edgeStates[eT] == -1 && edgeStates[eR] == 0) { if (!setEdgeState(eR, 1)) return false; }
                            if (edgeStates[eR] == -1 && edgeStates[eT] == 0) { if (!setEdgeState(eT, 1)) return false; }
                        }
                        // Up-Right dot is eT, eR. Opposite is eB, eL.
                        if (checkZeroLineAssumption(r, c, -1, 1)) {
                            if (edgeStates[eB] == -1 && edgeStates[eL] == 0) { if (!setEdgeState(eL, 1)) return false; }
                            if (edgeStates[eL] == -1 && edgeStates[eB] == 0) { if (!setEdgeState(eB, 1)) return false; }
                        }
                        // Up-Left dot is eT, eL. Opposite is eB, eR.
                        if (checkZeroLineAssumption(r, c, -1, -1)) {
                            if (edgeStates[eB] == -1 && edgeStates[eR] == 0) { if (!setEdgeState(eR, 1)) return false; }
                            if (edgeStates[eR] == -1 && edgeStates[eB] == 0) { if (!setEdgeState(eB, 1)) return false; }
                        }
                    }
                    
                    // Universal SLE Propagation
                    // If any corner has exactly 1 line and 1 cross, it shoots an SLE diagonally.
                    int eT = cellEdges[0];
                    int eR = cellEdges[1];
                    int eB = cellEdges[2];
                    int eL = cellEdges[3];
                    if (edgeStates[eT] != 0 && edgeStates[eL] != 0 && edgeStates[eT] != edgeStates[eL]) {
                        if (!propagateDiagonal2s(r - 1, c - 1, -1, -1)) return false;
                    }
                    if (edgeStates[eT] != 0 && edgeStates[eR] != 0 && edgeStates[eT] != edgeStates[eR]) {
                        if (!propagateDiagonal2s(r - 1, c + 1, -1, 1)) return false;
                    }
                    if (edgeStates[eB] != 0 && edgeStates[eL] != 0 && edgeStates[eB] != edgeStates[eL]) {
                        if (!propagateDiagonal2s(r + 1, c - 1, 1, -1)) return false;
                    }
                    if (edgeStates[eB] != 0 && edgeStates[eR] != 0 && edgeStates[eB] != edgeStates[eR]) {
                        if (!propagateDiagonal2s(r + 1, c + 1, 1, 1)) return false;
                    }
                    
                    if (clue == 2) {
                        // "2 and 3 diagonally adjacent with an external cross" deduction rule
                        // Bottom-Right
                        if (r + 1 < rows && c + 1 < cols && clues[(r + 1) * cols + (c + 1)] == 3) {
                            int tA = getHEdgeIndex(r, c);
                            int lA = getVEdgeIndex(r, c);
                            if (edgeStates[tA] == -1 || edgeStates[lA] == -1) {
                                if (edgeStates[tA] == -1) { if (!setEdgeState(lA, 1)) return false; }
                                if (edgeStates[lA] == -1) { if (!setEdgeState(tA, 1)) return false; }
                                int rB = getVEdgeIndex(r + 1, c + 2);
                                int bB = getHEdgeIndex(r + 2, c + 1);
                                if (!setEdgeState(rB, 1)) return false;
                                if (!setEdgeState(bB, 1)) return false;
                            }
                        }
                        // Bottom-Left
                        if (r + 1 < rows && c - 1 >= 0 && clues[(r + 1) * cols + (c - 1)] == 3) {
                            int tB = getHEdgeIndex(r, c);
                            int rB = getVEdgeIndex(r, c + 1);
                            if (edgeStates[tB] == -1 || edgeStates[rB] == -1) {
                                if (edgeStates[tB] == -1) { if (!setEdgeState(rB, 1)) return false; }
                                if (edgeStates[rB] == -1) { if (!setEdgeState(tB, 1)) return false; }
                                int lB = getVEdgeIndex(r + 1, c - 1);
                                int bB = getHEdgeIndex(r + 2, c - 1);
                                if (!setEdgeState(lB, 1)) return false;
                                if (!setEdgeState(bB, 1)) return false;
                            }
                        }
                        // Top-Right
                        if (r - 1 >= 0 && c + 1 < cols && clues[(r - 1) * cols + (c + 1)] == 3) {
                            int bC = getHEdgeIndex(r + 1, c);
                            int lC = getVEdgeIndex(r, c);
                            if (edgeStates[bC] == -1 || edgeStates[lC] == -1) {
                                if (edgeStates[bC] == -1) { if (!setEdgeState(lC, 1)) return false; }
                                if (edgeStates[lC] == -1) { if (!setEdgeState(bC, 1)) return false; }
                                int rC = getVEdgeIndex(r - 1, c + 2);
                                int tC = getHEdgeIndex(r - 1, c + 1);
                                if (!setEdgeState(rC, 1)) return false;
                                if (!setEdgeState(tC, 1)) return false;
                            }
                        }
                        // Top-Left
                        if (r - 1 >= 0 && c - 1 >= 0 && clues[(r - 1) * cols + (c - 1)] == 3) {
                            int bD = getHEdgeIndex(r + 1, c);
                            int rD = getVEdgeIndex(r, c + 1);
                            if (edgeStates[bD] == -1 || edgeStates[rD] == -1) {
                                if (edgeStates[bD] == -1) { if (!setEdgeState(rD, 1)) return false; }
                                if (edgeStates[rD] == -1) { if (!setEdgeState(bD, 1)) return false; }
                                int lD = getVEdgeIndex(r - 1, c - 1);
                                int tD = getHEdgeIndex(r - 1, c - 1);
                                if (!setEdgeState(lD, 1)) return false;
                                if (!setEdgeState(tD, 1)) return false;
                            }
                        }
                    }
                }
            }
            
            // 2. Process dots
            int dotIdx = dequeueDot();
            if (dotIdx != -1) {
                dbgSource = "dot";
                dbgDot = dotIdx;
                dbgCell = -1;
                int r = dotIdx / (cols + 1);
                int c = dotIdx % (cols + 1);
                int dotEdges[4];
                int dotEdgesCount = getDotEdges(r, c, dotEdges);
                int lines = 0;
                int crosses = 0;
                int undecided[4];
                int undecidedCount = 0;
                
                for (int j = 0; j < dotEdgesCount; j++) {
                    int idx = dotEdges[j];
                    if (edgeStates[idx] == 1) lines++;
                    else if (edgeStates[idx] == -1) crosses++;
                    else undecided[undecidedCount++] = idx;
                }
                
                if (lines > 2) {
                    return false; // Contradiction: degree limit exceeded
                }
                
                if (undecidedCount > 0) {
                    if (lines == 2) {
                        for (int j = 0; j < undecidedCount; j++) {
                            if (!setEdgeState(undecided[j], -1)) {
                                return false;
                            }
                        }
                    } else if (lines == 1 && undecidedCount == 1) {
                        if (!setEdgeState(undecided[0], 1)) {
                            return false;
                        }
                    } else if (lines == 0 && undecidedCount == 1) {
                        if (!setEdgeState(undecided[0], -1)) {
                            return false;
                        }
                    } else if (lines == 0 && undecidedCount == 2) {
                        // Rule A: Generalized Corner Heuristic
                        int e1 = undecided[0];
                        int e2 = undecided[1];
                        bool e1IsH = (e1 < numH);
                        bool e2IsH = (e2 < numH);
                        if (e1IsH != e2IsH) {
                            int hEdge = e1IsH ? e1 : e2;
                            int vEdge = e1IsH ? e2 : e1;
                            int hr = hEdge / cols;
                            int hc = hEdge % cols;
                            int vr = (vEdge - numH) / (cols + 1);
                            int vc = (vEdge - numH) % (cols + 1);
                            
                            int cr = -1, cc = -1;
                            if (hc == c && vr == r) {
                                cr = r; cc = c;
                            } else if (hc == c - 1 && vr == r) {
                                cr = r; cc = c - 1;
                            } else if (hc == c && vr == r - 1) {
                                cr = r - 1; cc = c;
                            } else if (hc == c - 1 && vr == r - 1) {
                                cr = r - 1; cc = c - 1;
                            }
                            
                            if (cr >= 0 && cr < rows && cc >= 0 && cc < cols) {
                                int cellIdx = cr * cols + cc;
                                int clue = clues[cellIdx];
                                if (clue == 3) {
                                    if (!setEdgeState(e1, 1)) return false;
                                    if (!setEdgeState(e2, 1)) return false;
                                } else if (clue == 1) {
                                    if (!setEdgeState(e1, -1)) return false;
                                    if (!setEdgeState(e2, -1)) return false;
                                }
                            }
                        }
                    }
                } else {
                    if (lines != 0 && lines != 2) {
                        return false; // Contradiction: degree must be 0 or 2
                    }
                }

                // 3. Advanced Rule: Line entering a 3 corner
                int eL = getHEdgeIndex(r, c - 1);
                int eR = getHEdgeIndex(r, c);
                int eT = getVEdgeIndex(r - 1, c);
                int eB = getVEdgeIndex(r, c);
                
                // Bottom-Right cell (cr=r, cc=c)
                if (getClue(r, c) == 3) {
                    if ((edgeStates[eL] == 1) || (edgeStates[eT] == 1)) {
                        if (edgeStates[eL] != 1) { if (!setEdgeState(eL, -1)) return false; }
                        if (edgeStates[eT] != 1) { if (!setEdgeState(eT, -1)) return false; }
                        if (!setEdgeState(getHEdgeIndex(r + 1, c), 1)) return false;
                        if (!setEdgeState(getVEdgeIndex(r, c + 1), 1)) return false;
                    }
                }
                // Bottom-Left cell (cr=r, cc=c-1)
                if (getClue(r, c - 1) == 3) {
                    if ((edgeStates[eR] == 1) || (edgeStates[eT] == 1)) {
                        if (edgeStates[eR] != 1) { if (!setEdgeState(eR, -1)) return false; }
                        if (edgeStates[eT] != 1) { if (!setEdgeState(eT, -1)) return false; }
                        if (!setEdgeState(getHEdgeIndex(r + 1, c - 1), 1)) return false;
                        if (!setEdgeState(getVEdgeIndex(r, c - 1), 1)) return false;
                    }
                }
                // Top-Right cell (cr=r-1, cc=c)
                if (getClue(r - 1, c) == 3) {
                    if ((edgeStates[eL] == 1) || (edgeStates[eB] == 1)) {
                        if (edgeStates[eL] != 1) { if (!setEdgeState(eL, -1)) return false; }
                        if (edgeStates[eB] != 1) { if (!setEdgeState(eB, -1)) return false; }
                        if (!setEdgeState(getHEdgeIndex(r - 1, c), 1)) return false;
                        if (!setEdgeState(getVEdgeIndex(r - 1, c + 1), 1)) return false;
                    }
                }
                // Top-Left cell (cr=r-1, cc=c-1)
                if (getClue(r - 1, c - 1) == 3) {
                    if ((edgeStates[eR] == 1) || (edgeStates[eB] == 1)) {
                        if (edgeStates[eR] != 1) { if (!setEdgeState(eR, -1)) return false; }
                        if (edgeStates[eB] != 1) { if (!setEdgeState(eB, -1)) return false; }
                        if (!setEdgeState(getHEdgeIndex(r - 1, c - 1), 1)) return false;
                        if (!setEdgeState(getVEdgeIndex(r - 1, c - 1), 1)) return false;
                    }
                }
                
                // 4. Generalized Rule: Line entering a 2 corner with opposite cross
                // Bottom-Right cell (cr=r, cc=c)
                if (getClue(r, c) == 2) {
                    if ((edgeStates[eL] == 1) || (edgeStates[eT] == 1)) {
                        int oppB = getHEdgeIndex(r + 1, c);
                        int oppR = getVEdgeIndex(r, c + 1);
                        if (edgeStates[oppB] == -1 || edgeStates[oppR] == -1) {
                            if (edgeStates[eL] != 1) { if (!setEdgeState(eL, -1)) return false; }
                            if (edgeStates[eT] != 1) { if (!setEdgeState(eT, -1)) return false; }
                            if (edgeStates[oppB] == -1) { if (!setEdgeState(oppR, 1)) return false; }
                            if (edgeStates[oppR] == -1) { if (!setEdgeState(oppB, 1)) return false; }
                        }
                    }
                }
                // Bottom-Left cell (cr=r, cc=c-1)
                if (getClue(r, c - 1) == 2) {
                    if ((edgeStates[eR] == 1) || (edgeStates[eT] == 1)) {
                        int oppB = getHEdgeIndex(r + 1, c - 1);
                        int oppL = getVEdgeIndex(r, c - 1);
                        if (edgeStates[oppB] == -1 || edgeStates[oppL] == -1) {
                            if (edgeStates[eR] != 1) { if (!setEdgeState(eR, -1)) return false; }
                            if (edgeStates[eT] != 1) { if (!setEdgeState(eT, -1)) return false; }
                            if (edgeStates[oppB] == -1) { if (!setEdgeState(oppL, 1)) return false; }
                            if (edgeStates[oppL] == -1) { if (!setEdgeState(oppB, 1)) return false; }
                        }
                    }
                }
                // Top-Right cell (cr=r-1, cc=c)
                if (getClue(r - 1, c) == 2) {
                    if ((edgeStates[eL] == 1) || (edgeStates[eB] == 1)) {
                        int oppT = getHEdgeIndex(r - 1, c);
                        int oppR = getVEdgeIndex(r - 1, c + 1);
                        if (edgeStates[oppT] == -1 || edgeStates[oppR] == -1) {
                            if (edgeStates[eL] != 1) { if (!setEdgeState(eL, -1)) return false; }
                            if (edgeStates[eB] != 1) { if (!setEdgeState(eB, -1)) return false; }
                            if (edgeStates[oppT] == -1) { if (!setEdgeState(oppR, 1)) return false; }
                            if (edgeStates[oppR] == -1) { if (!setEdgeState(oppT, 1)) return false; }
                        }
                    }
                }
                // Top-Left cell (cr=r-1, cc=c-1)
                if (getClue(r - 1, c - 1) == 2) {
                    if ((edgeStates[eR] == 1) || (edgeStates[eB] == 1)) {
                        int oppT = getHEdgeIndex(r - 1, c - 1);
                        int oppL = getVEdgeIndex(r - 1, c - 1);
                        if (edgeStates[oppT] == -1 || edgeStates[oppL] == -1) {
                            if (edgeStates[eR] != 1) { if (!setEdgeState(eR, -1)) return false; }
                            if (edgeStates[eB] != 1) { if (!setEdgeState(eB, -1)) return false; }
                            if (edgeStates[oppT] == -1) { if (!setEdgeState(oppL, 1)) return false; }
                            if (edgeStates[oppL] == -1) { if (!setEdgeState(oppT, 1)) return false; }
                        }
                    }
                }
                // 5. Diagonal 2s Propagation Rule
                bool sle_TL = (eT != -1) && ((edgeStates[eL] == 1 && edgeStates[eT] == -1) || (edgeStates[eL] == -1 && edgeStates[eT] == 1));
                bool sle_TR = (eT != -1) && ((edgeStates[eR] == 1 && edgeStates[eT] == -1) || (edgeStates[eR] == -1 && edgeStates[eT] == 1));
                bool sle_BL = (eB != -1) && ((edgeStates[eL] == 1 && edgeStates[eB] == -1) || (edgeStates[eL] == -1 && edgeStates[eB] == 1));
                bool sle_BR = (eB != -1) && ((edgeStates[eR] == 1 && edgeStates[eB] == -1) || (edgeStates[eR] == -1 && edgeStates[eB] == 1));

                if (sle_BR && getClue(r - 1, c - 1) == 2) {
                    if (!propagateDiagonal2s(r - 1, c - 1, -1, -1)) return false;
                }
                if (sle_BL && getClue(r - 1, c) == 2) {
                    if (!propagateDiagonal2s(r - 1, c, -1, 1)) return false;
                }
                if (sle_TR && getClue(r, c - 1) == 2) {
                    if (!propagateDiagonal2s(r, c - 1, 1, -1)) return false;
                }
                if (sle_TL && getClue(r, c) == 2) {
                    if (!propagateDiagonal2s(r, c, 1, 1)) return false;
                }
            }
        }
        
        // Queues are empty. Check Jordan Curve Parity, Corner 2 rules, and 2-cell corner parity!
        if (!deductJordanCurveParity()) return false;
        if (!applyAdvanced2Rules()) return false;
        
        for (int r = 0; r < rows; r++) {
            for (int c = 0; c < cols; c++) {
                if (clues[r * cols + c] == 2) {
                    int tl_v = getVEdgeIndex(r - 1, c);
                    int tl_h = getHEdgeIndex(r, c - 1);
                    int br_v = getVEdgeIndex(r + 1, c + 1);
                    int br_h = getHEdgeIndex(r + 1, c + 1);
                    if (!deductParityPair(tl_v, tl_h, br_v, br_h)) return false;
                    
                    int tr_v = getVEdgeIndex(r - 1, c + 1);
                    int tr_h = getHEdgeIndex(r, c + 1);
                    int bl_v = getVEdgeIndex(r + 1, c);
                    int bl_h = getHEdgeIndex(r + 1, c - 1);
                    if (!deductParityPair(tr_v, tr_h, bl_v, bl_h)) return false;
                }
            }
        }
        
        bool cycleChanged = false;
        for (int i = 0; i < numEdges; i++) {
            if (edgeStates[i] == 0) {
                int dotA, dotB;
                if (i < numH) {
                    int rr = i / cols;
                    int cc = i % cols;
                    dotA = rr * (cols + 1) + cc;
                    dotB = dotA + 1;
                } else {
                    int vIdx = i - numH;
                    int rr = vIdx / (cols + 1);
                    int cc = vIdx % (cols + 1);
                    dotA = rr * (cols + 1) + cc;
                    dotB = dotA + (cols + 1);
                }
                if (dsuFind(dotA) == dsuFind(dotB)) {
                    edgeStates[i] = 1;
                    bool solved = isSolved();
                    edgeStates[i] = 0;
                    if (!solved) {
                        if (!setEdgeState(i, -1)) return false;
                        if (edgeStates[i] == -1) cycleChanged = true;
                    }
                }
            }
        }
        
        if (cellQueueHead == cellQueueTail && dotQueueHead == dotQueueTail && !cycleChanged) {
            break;
        }
    }
    return true;
}

EMSCRIPTEN_KEEPALIVE
bool deduct() {
    dsuInitFromCurrent();
    clearQueues();
    
    // Seed queues with all cells and dots
    for (int r = 0; r < rows; r++) {
        for (int c = 0; c < cols; c++) {
            enqueueCell(r, c);
        }
    }
    for (int r = 0; r <= rows; r++) {
        for (int c = 0; c <= cols; c++) {
            enqueueDot(r, c);
        }
    }
    
    if (!applyStaticRules()) {
        return false;
    }
    
    return deductIncremental();
}

// SOLVED STATE VERIFICATION
EMSCRIPTEN_KEEPALIVE
bool isSolved() {
    // Undecided edges check removed to allow leaf pruning. Complete checks are handled during backtracking leaves.

    for (int r = 0; r < rows; r++) {
        for (int c = 0; c < cols; c++) {
            int clue = clues[r * cols + c];
            if (clue == -1) continue;

            int cellEdges[4];
            getCellEdges(r, c, cellEdges);
            int lines = 0;
            for (int j = 0; j < 4; j++) {
                if (edgeStates[cellEdges[j]] == 1) lines++;
            }
            if (lines != clue) return false;
        }
    }

    memset(adjCount, 0, sizeof(adjCount));
    int edgeCount = 0;

    for (int r = 0; r <= rows; r++) {
        for (int c = 0; c <= cols; c++) {
            int dotId = r * (cols + 1) + c;
            if (c < cols) {
                int hIdx = r * cols + c;
                if (edgeStates[hIdx] == 1) {
                    int neighbor = dotId + 1;
                    adj[dotId][adjCount[dotId]++] = neighbor;
                    adj[neighbor][adjCount[neighbor]++] = dotId;
                    edgeCount++;
                }
            }
            if (r < rows) {
                int vIdx = numH + r * (cols + 1) + c;
                if (edgeStates[vIdx] == 1) {
                    int neighbor = dotId + (cols + 1);
                    adj[dotId][adjCount[dotId]++] = neighbor;
                    adj[neighbor][adjCount[neighbor]++] = dotId;
                    edgeCount++;
                }
            }
        }
    }

    if (edgeCount == 0) return false;

    int startDot = -1;
    for (int i = 0; i < numDots; i++) {
        int deg = adjCount[i];
        if (deg != 0 && deg != 2) return false;
        if (deg == 2 && startDot == -1) {
            startDot = i;
        }
    }

    if (startDot == -1) return false;

    memset(visitedDots, 0, sizeof(visitedDots));
    int curr = startDot;
    int prev = -1;
    int visitedCount = 0;

    while (true) {
        visitedDots[curr] = true;
        visitedCount++;

        int next = -1;
        for (int j = 0; j < adjCount[curr]; j++) {
            int n = adj[curr][j];
            if (n != prev) {
                next = n;
                break;
            }
        }

        if (next == -1) return false;

        if (visitedDots[next]) {
            if (next == startDot) break;
            return false; // Intersects itself
        }

        prev = curr;
        curr = next;
    }

    int activeDots = 0;
    for (int i = 0; i < numDots; i++) {
        if (adjCount[i] == 2) activeDots++;
    }

    return visitedCount == activeDots;
}


// BACKTRACK ENGINE
#define MAX_SOLUTIONS 2
static int8_t foundSolutions[MAX_SOLUTIONS][MAX_EDGES];
static int foundSolutionsCount = 0;
static int explorationSteps = 0;
static bool isTimeout = false;

static void backtrack(int depth, bool findSingle, int maxSteps) {
    explorationSteps++;
    if (explorationSteps > maxSteps) {
        isTimeout = true;
        return;
    }

    if (depth >= MAX_BACKTRACK_DEPTH) {
        return;
    }

    // Save global edge states, DSU history
    memcpy(backupStack[depth], edgeStates, numEdges);
    int dsuCheckpoint = dsuHistoryCount;

    // Run logical deduction rules: full pass at depth 0, incremental pass at depth > 0
    if (depth == 0) {
        if (!deduct()) {
            memcpy(edgeStates, backupStack[depth], numEdges);
            clearQueues();
            dsuRollback(dsuCheckpoint);
            return;
        }
    } else {
        if (!deductIncremental()) {
            memcpy(edgeStates, backupStack[depth], numEdges);
            clearQueues();
            dsuRollback(dsuCheckpoint);
            return;
        }
    }

    int undecidedIdx = -1;
    for (int i = 0; i < numEdges; i++) {
        if (edgeStates[i] == 0) {
            undecidedIdx = i;
            break;
        }
    }

    if (undecidedIdx == -1) {
        if (isSolved()) {
            if (foundSolutionsCount < MAX_SOLUTIONS) {
                int8_t* sol = foundSolutions[foundSolutionsCount++];
                memcpy(sol, edgeStates, numEdges);
            }
        }
        memcpy(edgeStates, backupStack[depth], numEdges);
        clearQueues();
        dsuRollback(dsuCheckpoint);
        return;
    }

    if (foundSolutionsCount >= 2 || (findSingle && foundSolutionsCount >= 1)) {
        memcpy(edgeStates, backupStack[depth], numEdges);
        clearQueues();
        dsuRollback(dsuCheckpoint);
        return;
    }

    // Save state AFTER deduction
    memcpy(backupAfterDeductStack[depth], edgeStates, numEdges);
    int dsuCheckpointAfterDeduct = dsuHistoryCount;

    int branchIdx = -1;
    int minUndecided = 999;

    for (int r = 0; r < rows; r++) {
        for (int c = 0; c < cols; c++) {
            int clue = clues[r * cols + c];
            if (clue != -1) {
                int cellEdges[4];
                getCellEdges(r, c, cellEdges);
                int undecidedCount = 0;
                int firstUndecided = -1;
                
                for (int j = 0; j < 4; j++) {
                    if (edgeStates[cellEdges[j]] == 0) {
                        undecidedCount++;
                        if (firstUndecided == -1) {
                            firstUndecided = cellEdges[j];
                        }
                    }
                }
                
                if (undecidedCount > 0 && undecidedCount < minUndecided) {
                    minUndecided = undecidedCount;
                    branchIdx = firstUndecided;
                    if (minUndecided == 1) {
                        break; // Most constrained possible
                    }
                }
            }
        }
        if (minUndecided == 1) {
            break;
        }
    }

    if (branchIdx == -1) {
        branchIdx = undecidedIdx; // Fallback
    }

    // Try setting edge to 1 (line)
    if (setEdgeState(branchIdx, 1)) {
        backtrack(depth + 1, findSingle, maxSteps);
    }
    dsuRollback(dsuCheckpointAfterDeduct);
    memcpy(edgeStates, backupAfterDeductStack[depth], numEdges);
    clearQueues();

    if (foundSolutionsCount >= 2 || (findSingle && foundSolutionsCount >= 1) || isTimeout) {
        dsuRollback(dsuCheckpoint);
        memcpy(edgeStates, backupStack[depth], numEdges);
        clearQueues();
        return;
    }

    // Try setting edge to -1 (cross)
    if (setEdgeState(branchIdx, -1)) {
        backtrack(depth + 1, findSingle, maxSteps);
    }
    dsuRollback(dsuCheckpointAfterDeduct);
    memcpy(edgeStates, backupAfterDeductStack[depth], numEdges);
    clearQueues();
    
    // Cleanup to restore parent state
    dsuRollback(dsuCheckpoint);
    memcpy(edgeStates, backupStack[depth], numEdges);
    clearQueues();
}

double calculateConsecutive3Penalty() {
    double totalPenalty = 0.0;
    static bool visitedH[MAX_ROWS][MAX_COLS];
    static bool visitedV[MAX_ROWS][MAX_COLS];
    static bool visitedDR[MAX_ROWS][MAX_COLS]; // Down-Right
    static bool visitedDL[MAX_ROWS][MAX_COLS]; // Down-Left
    
    memset(visitedH, 0, sizeof(visitedH));
    memset(visitedV, 0, sizeof(visitedV));
    memset(visitedDR, 0, sizeof(visitedDR));
    memset(visitedDL, 0, sizeof(visitedDL));
    
    for (int r = 0; r < rows; r++) {
        for (int c = 0; c < cols; c++) {
            if (clues[r * cols + c] == 3) {
                // 1. Horizontal Chain
                if (!visitedH[r][c]) {
                    int L = 0;
                    while (c + L < cols && clues[r * cols + (c + L)] == 3) {
                        visitedH[r][c + L] = true;
                        L++;
                    }
                    if (L >= 4) totalPenalty += 100.0 * pow(3.0, L - 3);
                }
                
                // 2. Vertical Chain
                if (!visitedV[r][c]) {
                    int L = 0;
                    while (r + L < rows && clues[(r + L) * cols + c] == 3) {
                        visitedV[r + L][c] = true;
                        L++;
                    }
                    if (L >= 4) totalPenalty += 100.0 * pow(3.0, L - 3);
                }
                
                // 3. Diagonal Down-Right
                if (!visitedDR[r][c]) {
                    int L = 0;
                    while (r + L < rows && c + L < cols && clues[(r + L) * cols + (c + L)] == 3) {
                        visitedDR[r + L][c + L] = true;
                        L++;
                    }
                    if (L >= 4) totalPenalty += 100.0 * pow(3.0, L - 3);
                }
                
                // 4. Diagonal Down-Left
                if (!visitedDL[r][c]) {
                    int L = 0;
                    while (r + L < rows && c - L >= 0 && clues[(r + L) * cols + (c - L)] == 3) {
                        visitedDL[r + L][c - L] = true;
                        L++;
                    }
                    if (L >= 4) totalPenalty += 100.0 * pow(3.0, L - 3);
                }
            }
        }
    }
    return totalPenalty;
}

double calculateZigzagBendPenalty() {
    // Populate adj and adjCount from current edgeStates
    memset(adjCount, 0, sizeof(adjCount));
    for (int r = 0; r <= rows; r++) {
        for (int c = 0; c <= cols; c++) {
            int dotId = r * (cols + 1) + c;
            if (c < cols) {
                int hIdx = r * cols + c;
                if (edgeStates[hIdx] == 1) {
                    int neighborId = dotId + 1;
                    adj[dotId][adjCount[dotId]++] = neighborId;
                    adj[neighborId][adjCount[neighborId]++] = dotId;
                }
            }
            if (r < rows) {
                int vIdx = numH + r * (cols + 1) + c;
                if (edgeStates[vIdx] == 1) {
                    int neighborId = dotId + (cols + 1);
                    adj[dotId][adjCount[dotId]++] = neighborId;
                    adj[neighborId][adjCount[neighborId]++] = dotId;
                }
            }
        }
    }

    // 1. Find start vertex of the loop
    int startDot = -1;
    for (int i = 0; i < numDots; i++) {
        if (adjCount[i] == 2) { startDot = i; break; }
    }
    if (startDot == -1) return 0.0;

    // 2. Trace path vertices
    static int path[MAX_DOTS];
    int pathCount = 0;
    static bool visited[MAX_DOTS];
    memset(visited, 0, sizeof(visited));
    
    int curr = startDot, prev = -1;
    while (true) {
        path[pathCount++] = curr;
        visited[curr] = true;
        int next = -1;
        for (int j = 0; j < adjCount[curr]; j++) {
            if (adj[curr][j] != prev) { next = adj[curr][j]; break; }
        }
        if (next == -1 || next == startDot || visited[next]) break;
        prev = curr;
        curr = next;
    }
    if (pathCount < 4) return 0.0;

    // 3. Extract directions
    static int dirs[MAX_DOTS];
    int dirCount = 0;
    for (int i = 0; i < pathCount; i++) {
        int d1 = path[i], d2 = path[(i + 1) % pathCount];
        int r1 = d1 / (cols + 1), c1 = d1 % (cols + 1);
        int r2 = d2 / (cols + 1), c2 = d2 % (cols + 1);
        int dir = (r2 == r1-1) ? 0 : (r2 == r1+1) ? 1 : (c2 == c1-1) ? 2 : (c2 == c1+1) ? 3 : -1;
        if (dir != -1) dirs[dirCount++] = dir;
    }

    // 4. Compress collinear segments
    static int compDirs[MAX_DOTS];
    int compCount = 0;
    if (dirCount > 0) {
        compDirs[compCount++] = dirs[0];
        for (int i = 1; i < dirCount; i++) {
            if (dirs[i] != compDirs[compCount - 1]) compDirs[compCount++] = dirs[i];
        }
        if (compCount > 1 && compDirs[0] == compDirs[compCount - 1]) compCount--;
    }
    if (compCount < 4) return 0.0;

    // 5. Evaluate alternating bend chains
    double totalPenalty = 0.0;
    for (int i = 0; i < compCount; i++) {
        int L = 2;
        while (L < compCount && compDirs[(i + L) % compCount] == compDirs[(i + L - 2) % compCount]) {
            L++;
        }
        if (L >= 5) {
            // Guarantee maximality: ensure previous element did not alternate
            int prevIdx = (i - 1 + compCount) % compCount;
            if (compDirs[prevIdx] != compDirs[(i + 1) % compCount]) {
                totalPenalty += 150.0 * pow(2.5, L - 4);
            }
        }
    }
    return totalPenalty;
}

int check_human_solvability() {
    dsuInitFromCurrent();
    clearQueues();
    
    lookaheadConfirmedCount = 0;
    
    // 1. Seed AC-3 queue with all active cells/dots
    for (int r = 0; r < rows; r++) {
        for (int c = 0; c < cols; c++) enqueueCell(r, c);
    }
    for (int r = 0; r <= rows; r++) {
        for (int c = 0; c <= cols; c++) enqueueDot(r, c);
    }
    
    if (!applyStaticRules()) {
        return 0; // Contradiction
    }
    
    bool changed = true;
    int loopCount = 0;
    while (changed) {
        loopCount++;
        if (loopCount > 10000) {
            printf("[C ERROR] check_human_solvability infinite loop detected!\n");
            return 0; // Force stop
        }
        // Run Level 1-3 propagation
        if (!deductIncremental()) {
            return 0; // Contradiction
        }
        
        // Check if fully solved
        bool allDecided = true;
        for (int i = 0; i < numEdges; i++) {
            if (edgeStates[i] == 0) { allDecided = false; break; }
        }
        if (allDecided) {
            return isSolved() ? 1 : 0;
        }
        
        changed = false;
        
        // 2. Perform 1-Step Lookahead on Undecided Edges
        for (int i = 0; i < numEdges; i++) {
            if (edgeStates[i] == 0) {
                // Scenario A: Assume Line (1)
                int checkpoint = dsuHistoryCount;
                int8_t backupEdges[MAX_EDGES];
                memcpy(backupEdges, edgeStates, numEdges);
                
                lookaheadConfirmedCount = 0;
                isDoingLookahead = true;
                bool lineSuccess = setEdgeState(i, 1) && deductIncremental();
                isDoingLookahead = false;
                
                dsuRollback(checkpoint);
                memcpy(edgeStates, backupEdges, numEdges);
                clearQueues();
                
                if (!lineSuccess) {
                    // Line leads to contradiction -> Must be Cross (-1)
                    if (!setEdgeState(i, -1)) return 0;
                    changed = true;
                    break; // Restart main propagation loop
                }
                
                // Scenario B: Assume Cross (-1)
                checkpoint = dsuHistoryCount;
                memcpy(backupEdges, edgeStates, numEdges);
                
                lookaheadConfirmedCount = 0;
                isDoingLookahead = true;
                bool crossSuccess = setEdgeState(i, -1) && deductIncremental();
                isDoingLookahead = false;
                
                dsuRollback(checkpoint);
                memcpy(edgeStates, backupEdges, numEdges);
                clearQueues();
                
                if (!crossSuccess) {
                    // Cross leads to contradiction -> Must be Line (1)
                    if (!setEdgeState(i, 1)) return 0;
                    changed = true;
                    break; // Restart main propagation loop
                }
            }
        }
    }
    return -2; // Stalled: Not solvable by 1-step lookahead human logic
}

EMSCRIPTEN_KEEPALIVE
int solve_puzzle_wasm(bool findSingle, int maxSteps) {
    foundSolutionsCount = 0;
    explorationSteps = 0;
    isTimeout = false;
    memset(foundSolutions, 0, sizeof(foundSolutions));

    // Initialize DSU and seed it with initial active edges (if any)
    dsuInitFromCurrent();

    backtrack(0, findSingle, maxSteps);

    if (isTimeout) {
        return -1; // timed out
    }
    return foundSolutionsCount;
}

EMSCRIPTEN_KEEPALIVE
int8_t* get_solution_ptr(int idx) {
    if (idx < 0 || idx >= MAX_SOLUTIONS) return NULL;
    return foundSolutions[idx];
}

// -------------------------------------------------------------
// PUZZLE GENERATOR ENGINE IN C
// -------------------------------------------------------------

static inline int getCell(int r, int c, int8_t cells[MAX_ROWS][MAX_COLS]) {
    if (r < 0 || r >= rows || c < 0 || c >= cols) return 0;
    return cells[r][c];
}

// Inside 3x3 Outside Block check
static int count3x3OutsideBlocks(int8_t cells[MAX_ROWS][MAX_COLS]) {
    int count = 0;
    for (int r = 0; r < rows - 2; r++) {
        for (int c = 0; c < cols - 2; c++) {
            bool isAllOutside = true;
            for (int i = 0; i < 3; i++) {
                for (int j = 0; j < 3; j++) {
                    if (cells[r + i][c + j] != 0) {
                        isAllOutside = false;
                        break;
                    }
                }
                if (!isAllOutside) break;
            }
            if (isAllOutside) count++;
        }
    }
    return count;
}

// Check sector coverage
static bool checkSectorCoverage(int8_t cells[MAX_ROWS][MAX_COLS], int numSectorsX, int numSectorsY) {
    bool sectors[4][4];
    memset(sectors, 0, sizeof(sectors));

    for (int r = 0; r < rows; r++) {
        for (int c = 0; c < cols; c++) {
            if (cells[r][c] == 1) {
                int sy = (r * numSectorsY) / rows;
                int sx = (c * numSectorsX) / cols;
                if (sy >= 0 && sy < numSectorsY && sx >= 0 && sx < numSectorsX) {
                    sectors[sy][sx] = true;
                }
            }
        }
    }

    for (int sy = 0; sy < numSectorsY; sy++) {
        for (int sx = 0; sx < numSectorsX; sx++) {
            if (!sectors[sy][sx]) return false;
        }
    }
    return true;
}

// BFS check outside connectivity
static bool checkOutsideConnectivity(int8_t cells[MAX_ROWS][MAX_COLS]) {
    memset(visitedCells, 0, sizeof(visitedCells));
    int outsideCount = 0;
    int qHead = 0;
    int qTail = 0;

    for (int r = 0; r < rows; r++) {
        for (int c = 0; c < cols; c++) {
            if (cells[r][c] == 0) {
                outsideCount++;
                bool isBorder = (r == 0 || r == rows - 1 || c == 0 || c == cols - 1);
                if (isBorder) {
                    queueR[qTail] = r;
                    queueC[qTail] = c;
                    qTail++;
                    visitedCells[r][c] = true;
                }
            }
        }
    }

    if (outsideCount == 0) return false;
    if (qTail == 0 && outsideCount > 0) return false;

    int dr[] = {-1, 1, 0, 0};
    int dc[] = {0, 0, -1, 1};
    int reachedCount = 0;

    while (qHead < qTail) {
        int r = queueR[qHead];
        int c = queueC[qHead];
        qHead++;
        reachedCount++;

        for (int i = 0; i < 4; i++) {
            int nr = r + dr[i];
            int nc = c + dc[i];
            if (nr >= 0 && nr < rows && nc >= 0 && nc < cols) {
                if (cells[nr][nc] == 0 && !visitedCells[nr][nc]) {
                    visitedCells[nr][nc] = true;
                    queueR[qTail] = nr;
                    queueC[qTail] = nc;
                    qTail++;
                }
            }
        }
    }

    return reachedCount == outsideCount;
}

// Check if a cell configuration has any diagonal checkerboard (degree-4 vertices)
static bool hasDiagonalCheckerboard(int8_t cells[MAX_ROWS][MAX_COLS]) {
    for (int r = 0; r < rows - 1; r++) {
        for (int c = 0; c < cols - 1; c++) {
            int tl = cells[r][c];
            int tr = cells[r][c + 1];
            int bl = cells[r + 1][c];
            int br = cells[r + 1][c + 1];
            if (tl == br && tr == bl && tl != tr) {
                return true;
            }
        }
    }
    return false;
}

// Growth Loop Generator
static void generateRandomLoop() {
    int numSectorsX = cols >= 24 ? 4 : (cols >= 8 ? 3 : 2);
    int numSectorsY = rows >= 12 ? 4 : (rows >= 8 ? 3 : 2);
    int totalCells = rows * cols;

    int attempts = 0;
    int maxAttempts = 40;
    bool success = false;

    while (attempts < maxAttempts && !success) {
        attempts++;
        memset(genCells, 0, sizeof(genCells)); // 0 = Outside, 1 = Inside

        // Pick a random start cell
        int startR = rand() % rows;
        int startC = rand() % cols;
        genCells[startR][startC] = 1;

        double fillRatioMin = 0.60;
        double fillRatioMax = 0.75;
        if (totalCells <= 36) {
            fillRatioMin = 0.35;
            fillRatioMax = 0.47;
        } else if (totalCells <= 64) {
            fillRatioMin = 0.42;
            fillRatioMax = 0.54;
        } else if (totalCells <= 144) {
            fillRatioMin = 0.46;
            fillRatioMax = 0.58;
        }

        int targetInsideCount = (int)(totalCells * (fillRatioMin + ((double)rand() / RAND_MAX) * (fillRatioMax - fillRatioMin)));
        int insideCount = 1;

        int failedAttempts = 0;
        int maxFailedAttempts = 300;
        int dr[] = {-1, 1, 0, 0};
        int dc[] = {0, 0, -1, 1};

        bool shouldBreakOutside = false;

        while ((insideCount < targetInsideCount || (shouldBreakOutside && count3x3OutsideBlocks(genCells) > 0)) && failedAttempts < maxFailedAttempts) {
            // Find Candidate cells with weighted score
            int sumR = 0, sumC = 0;
            for (int r = 0; r < rows; r++) {
                for (int c = 0; c < cols; c++) {
                    if (genCells[r][c] == 1) {
                        sumR += r;
                        sumC += c;
                    }
                }
            }
            double avgR = (double)sumR / insideCount;
            double avgC = (double)sumC / insideCount;

            // Calculate sector density
            int sectorCounts[4][4];
            memset(sectorCounts, 0, sizeof(sectorCounts));
            for (int r = 0; r < rows; r++) {
                for (int c = 0; c < cols; c++) {
                    if (genCells[r][c] == 1) {
                        int sy = (r * numSectorsY) / rows;
                        int sx = (c * numSectorsX) / cols;
                        if (sy >= 0 && sy < numSectorsY && sx >= 0 && sx < numSectorsX) {
                            sectorCounts[sy][sx]++;
                        }
                    }
                }
            }

            // Build Candidate list
            static Candidate candidates[MAX_CELLS];
            int candCount = 0;

            for (int r = 0; r < rows; r++) {
                for (int c = 0; c < cols; c++) {
                    if (genCells[r][c] == 0) {
                        int insideNeighbors = 0;
                        int firstNeighborR = -1;
                        int firstNeighborC = -1;

                        for (int i = 0; i < 4; i++) {
                            int nr = r + dr[i];
                            int nc = c + dc[i];
                            if (nr >= 0 && nr < rows && nc >= 0 && nc < cols && genCells[nr][nc] == 1) {
                                insideNeighbors++;
                                if (firstNeighborR == -1) {
                                    firstNeighborR = nr;
                                    firstNeighborC = nc;
                                }
                            }
                        }

                        // Inside 4x4 block restriction
                        bool wouldForm4x4Inside = false;
                        for (int dy = -3; dy <= 0; dy++) {
                            for (int dx = -3; dx <= 0; dx++) {
                                int count = 0;
                                for (int i = 0; i < 4; i++) {
                                    for (int j = 0; j < 4; j++) {
                                        int nr = r + dy + i;
                                        int nc = c + dx + j;
                                        if (nr == r && nc == c) continue;
                                        if (nr >= 0 && nr < rows && nc >= 0 && nc < cols && genCells[nr][nc] == 1) {
                                            count++;
                                        }
                                    }
                                }
                                if (count == 15) {
                                    wouldForm4x4Inside = true;
                                    break;
                                }
                            }
                            if (wouldForm4x4Inside) break;
                        }

                        // Diagonal checkerboard prevention
                        bool wouldFormCheckerboard = false;
                        int diagonalsR[] = {-1, -1, 1, 1};
                        int diagonalsC[] = {-1, 1, -1, 1};
                        int adjR1[] = {-1, -1, 1, 1};
                        int adjC1[] = {0, 0, 0, 0};
                        int adjR2[] = {0, 0, 0, 0};
                        int adjC2[] = {-1, 1, -1, 1};
                        for (int i = 0; i < 4; i++) {
                            int drDiag = diagonalsR[i];
                            int dcDiag = diagonalsC[i];
                            int nrDiag = r + drDiag;
                            int ncDiag = c + dcDiag;
                            if (nrDiag >= 0 && nrDiag < rows && ncDiag >= 0 && ncDiag < cols) {
                                if (genCells[nrDiag][ncDiag] == 1) {
                                    int ar1 = r + adjR1[i];
                                    int ac1 = c + adjC1[i];
                                    int ar2 = r + adjR2[i];
                                    int ac2 = c + adjC2[i];
                                    if (genCells[ar1][ac1] == 0 && genCells[ar2][ac2] == 0) {
                                        wouldFormCheckerboard = true;
                                        break;
                                    }
                                }
                            }
                        }

                        if (insideNeighbors > 0 && insideNeighbors < 4 && !wouldForm4x4Inside && !wouldFormCheckerboard) {
                            double neighborScore = (insideNeighbors == 1) ? 8.0 : ((insideNeighbors == 2) ? 5.0 : 1.0);
                            double dist = sqrt(pow(r - avgR, 2) + pow(c - avgC, 2));
                            double distScore = 1.0 + dist * 0.25;

                            bool isBorder = (r == 0 || r == rows - 1 || c == 0 || c == cols - 1);
                            double borderPenalty = 1.0;
                            if (isBorder) {
                                borderPenalty = (totalCells <= 64) ? 0.35 : 0.65;
                            }

                            double bendMultiplier = 1.0;
                            if (insideNeighbors == 1 && firstNeighborR != -1) {
                                int secondNeighborsCount = 0;
                                int secondR = -1, secondC = -1;
                                for (int j = 0; j < 4; j++) {
                                    int nnr = firstNeighborR + dr[j];
                                    int nnc = firstNeighborC + dc[j];
                                    if (nnr >= 0 && nnr < rows && nnc >= 0 && nnc < cols && genCells[nnr][nnc] == 1) {
                                        secondR = nnr;
                                        secondC = nnc;
                                        secondNeighborsCount++;
                                    }
                                }

                                  if (secondNeighborsCount == 1) {
                                      bool isCollinear = (r == firstNeighborR && firstNeighborR == secondR) || 
                                                         (c == firstNeighborC && firstNeighborC == secondC);
                                      bool isBorder = (r == 0 || r == rows - 1 || c == 0 || c == cols - 1);
                                      if (isCollinear) bendMultiplier = isBorder ? 0.25 : 0.90;
                                      else bendMultiplier = isBorder ? 2.20 : 1.10;
                                  }
                            }

                            double sectorBonus = 1.0;
                            int sy = (r * numSectorsY) / rows;
                            int sx = (c * numSectorsX) / cols;
                            if (sy >= 0 && sy < numSectorsY && sx >= 0 && sx < numSectorsX) {
                                if (sectorCounts[sy][sx] == 0) {
                                    sectorBonus = 6.0; // Draw loop to empty sectors
                                }
                            }

                            int brokenOutsideBlocks = 0;
                            for (int dy = -2; dy <= 0; dy++) {
                                for (int dx = -2; dx <= 0; dx++) {
                                    bool isAllOutside = true;
                                    for (int i = 0; i < 3; i++) {
                                        for (int j = 0; j < 3; j++) {
                                            int nr = r + dy + i;
                                            int nc = c + dx + j;
                                            if (nr == r && nc == c) continue;
                                            if (nr >= 0 && nr < rows && nc >= 0 && nc < cols && genCells[nr][nc] != 0) {
                                                isAllOutside = false;
                                                break;
                                            }
                                        }
                                        if (!isAllOutside) break;
                                    }
                                    if (isAllOutside) brokenOutsideBlocks++;
                                }
                            }

                            double breakerBonus = 1.0;
                            if (brokenOutsideBlocks > 0) {
                                breakerBonus = 1.0 + 8.0 * brokenOutsideBlocks; // Block destroyer bonus
                            }

                            candidates[candCount].r = r;
                            candidates[candCount].c = c;
                            candidates[candCount].score = neighborScore * distScore * borderPenalty * bendMultiplier * sectorBonus * breakerBonus;
                            candCount++;
                        }
                    }
                }
            }

            if (candCount == 0) break;

            // Sort candidates desc
            for (int i = 0; i < candCount - 1; i++) {
                for (int j = i + 1; j < candCount; j++) {
                    if (candidates[j].score > candidates[i].score) {
                        Candidate temp = candidates[i];
                        candidates[i] = candidates[j];
                        candidates[j] = temp;
                    }
                }
            }

            // Pick randomly from top pool
            int poolSize = (candCount < 3) ? candCount : 3;
            int chosenIdx = rand() % poolSize;
            int cr = candidates[chosenIdx].r;
            int cc = candidates[chosenIdx].c;

            genCells[cr][cc] = 1;

            // Hole filling BFS
            memset(visitedCells, 0, sizeof(visitedCells));
            int qTail = 0;
            for (int r = 0; r < rows; r++) {
                for (int c = 0; c < cols; c++) {
                    if (genCells[r][c] == 0) {
                        bool isBorder = (r == 0 || r == rows - 1 || c == 0 || c == cols - 1);
                        if (isBorder) {
                            queueR[qTail] = r;
                            queueC[qTail] = c;
                            qTail++;
                            visitedCells[r][c] = true;
                        }
                    }
                }
            }

            int qHead = 0;
            while (qHead < qTail) {
                int r = queueR[qHead];
                int c = queueC[qHead];
                qHead++;
                for (int i = 0; i < 4; i++) {
                    int nr = r + dr[i];
                    int nc = c + dc[i];
                    if (nr >= 0 && nr < rows && nc >= 0 && nc < cols) {
                        if (genCells[nr][nc] == 0 && !visitedCells[nr][nc]) {
                            visitedCells[nr][nc] = true;
                            queueR[qTail] = nr;
                            queueC[qTail] = nc;
                            qTail++;
                        }
                    }
                }
            }

            static int filledR[MAX_CELLS];
            static int filledC[MAX_CELLS];
            int filledCount = 0;

            for (int r = 0; r < rows; r++) {
                for (int c = 0; c < cols; c++) {
                    if (genCells[r][c] == 0 && !visitedCells[r][c]) {
                        genCells[r][c] = 1;
                        filledR[filledCount] = r;
                        filledC[filledCount] = c;
                        filledCount++;
                    }
                }
            }

            // Verify 3x3 block check after filling holes
            bool has4x4Inside = false;
            for (int r = 0; r < rows - 3; r++) {
                for (int c = 0; c < cols - 3; c++) {
                    bool isAllInside = true;
                    for (int i = 0; i < 4; i++) {
                        for (int j = 0; j < 4; j++) {
                            if (genCells[r + i][c + j] != 1) {
                                isAllInside = false;
                                break;
                            }
                        }
                        if (!isAllInside) break;
                    }
                    if (isAllInside) {
                        has4x4Inside = true;
                        break;
                    }
                }
                if (has4x4Inside) break;
            }

            if (!has4x4Inside) {
                insideCount += 1 + filledCount;
                failedAttempts = 0;
            } else {
                // Revert choices
                genCells[cr][cc] = 0;
                for (int f = 0; f < filledCount; f++) {
                    genCells[filledR[f]][filledC[f]] = 0;
                }
                failedAttempts++;
            }
        }

        int minAcceptableInsideCount = (int)(targetInsideCount * 0.9);
        if (insideCount >= minAcceptableInsideCount && 
            checkSectorCoverage(genCells, numSectorsX, numSectorsY) && 
            !hasDiagonalCheckerboard(genCells)) {
            success = true;
        }
    }

    // Convert cell Inside/Outside representation to Loop Edges
    memset(edgeStates, -1, sizeof(edgeStates));
    for (int r = 0; r <= rows; r++) {
        for (int c = 0; c < cols; c++) {
            int topCell = getCell(r - 1, c, genCells);
            int bottomCell = getCell(r, c, genCells);
            if (topCell != bottomCell) {
                edgeStates[r * cols + c] = 1;
            }
        }
    }
    for (int r = 0; r < rows; r++) {
        for (int c = 0; c <= cols; c++) {
            int leftCell = getCell(r, c - 1, genCells);
            int rightCell = getCell(r, c, genCells);
            int idx = numH + r * (cols + 1) + c;
            if (leftCell != rightCell) {
                edgeStates[idx] = 1;
            }
        }
    }
}

// Calculate clues based on loop edge transitions
static void calculateClues() {
    memset(clues, -1, sizeof(clues));
    for (int r = 0; r < rows; r++) {
        for (int c = 0; c < cols; c++) {
            int state = genCells[r][c];
            int edgeCount = 0;

            if (state != getCell(r - 1, c, genCells)) edgeCount++;
            if (state != getCell(r + 1, c, genCells)) edgeCount++;
            if (state != getCell(r, c - 1, genCells)) edgeCount++;
            if (state != getCell(r, c + 1, genCells)) edgeCount++;

            clues[r * cols + c] = edgeCount;
        }
    }
}

static int debugTimeoutCount = 0;
static int debugContradictionCount = 0;
static int solvabilityChecks = 0;
static int fastPathCount = 0;

// Fast solver validation for minimization
static bool checkSolvability(const char* difficulty) {
    solvabilityChecks++;
    
    // Backup current edgeStates before solving
    static int8_t origEdges[MAX_EDGES];
    memcpy(origEdges, edgeStates, numEdges);
    
    memset(edgeStates, 0, numEdges);
    
    int result = 0;
    if (strcmp(difficulty, "easy") == 0) {
        // Easy mode: strict 0-step lookahead (pure deduction)
        bool deductSuccess = deduct();
        bool solvedSuccess = isSolved();
        bool allDecided = true;
        for (int i = 0; i < numEdges; i++) {
            if (edgeStates[i] == 0) {
                allDecided = false;
                break;
            }
        }
        
        if (deductSuccess && solvedSuccess && allDecided) {
            result = 1;
        } else {
            result = 0;
        }
    } else {
        // Set lookahead limits based on difficulty
        lookaheadConfirmedCount = 0;
        if (strcmp(difficulty, "medium") == 0) {
            lookaheadMaxLimit = 3;
        } else if (strcmp(difficulty, "hard") == 0) {
            lookaheadMaxLimit = 3;
        } else {
            lookaheadMaxLimit = 3; // expert
        }
        // Medium/Hard/Expert: 1-step lookahead human solvability check
        result = check_human_solvability();
        lookaheadMaxLimit = 0; // Reset limit
    }
    
    memcpy(edgeStates, origEdges, numEdges); // restore original
    
    if (result == 1) {
        fastPathCount++;
    } else if (result == 0) {
        debugContradictionCount++;
    } else if (result == -2) {
        debugContradictionCount++; // treat stalled as not solvable
    }
    
    return (result == 1);
}

// FULL MINIMIZATION ENGINE IN C (TOP-DOWN & SYMMETRIC)
EMSCRIPTEN_KEEPALIVE
void generate_puzzle_wasm(const char* difficulty) {
    debugTimeoutCount = 0;
    debugContradictionCount = 0;
    
    printf("[C Debug] Starting generate_puzzle_wasm. diff=%s, rows=%d, cols=%d\n", difficulty, rows, cols);

    // 1. Generate a random solved loop and calculate target clues until initial board is solvable
    bool initSolvable = false;
    int generateAttempts = 0;
    while (!initSolvable && generateAttempts < 200) {
        generateAttempts++;
        clock_t t0 = clock();
#ifdef __EMSCRIPTEN__
        EM_ASM({
            if (typeof self !== 'undefined' && typeof self.reportProgress === 'function') {
                self.reportProgress($0, -1);
            }
        }, generateAttempts);
#endif
        clock_t tProgress = clock();
        generateRandomLoop();
        clock_t tLoop = clock();
        calculateClues();
        clock_t tClues = clock();
        
        // Calculate penalties
        double p3 = calculateConsecutive3Penalty();
        double pZig = calculateZigzagBendPenalty();
        clock_t tPenalties = clock();
        
        // If penalties are too high, we reject this loop to ensure aesthetic quality
        if (p3 > 0.0 || pZig > 0.0) {
            int totalCells = rows * cols;
            double baseAllowed = (totalCells > 150) ? (totalCells - 150) * 80.0 : 0.0;
            double allowedPenalty = (generateAttempts < 5) ? baseAllowed : baseAllowed + (generateAttempts - 5) * 500.0;
            
            if (p3 + pZig > allowedPenalty) {
                printf("[C Debug] Attempt %d: Rejected by penalties. p3=%.1f, pZig=%.1f, allowed=%.1f | loopTime=%.1fms\n",
                       generateAttempts, p3, pZig, allowedPenalty, (double)(tLoop - tProgress) * 1000.0 / CLOCKS_PER_SEC);
                continue; // Reject loop
            }
        }
        
        initSolvable = checkSolvability(difficulty);
        clock_t tSolvable = clock();
        
        printf("[C Debug] Attempt %d: progress=%.1fms, loop=%.1fms, clues=%.1fms, penalties=%.1fms, solvable=%.1fms (solvable=%d)\n",
               generateAttempts,
               (double)(tProgress - t0) * 1000.0 / CLOCKS_PER_SEC,
               (double)(tLoop - tProgress) * 1000.0 / CLOCKS_PER_SEC,
               (double)(tClues - tLoop) * 1000.0 / CLOCKS_PER_SEC,
               (double)(tPenalties - tClues) * 1000.0 / CLOCKS_PER_SEC,
               (double)(tSolvable - tPenalties) * 1000.0 / CLOCKS_PER_SEC,
               initSolvable);
    }

    // Store target loop and clues
    static int8_t targetEdgeStates[MAX_EDGES];
    memcpy(targetEdgeStates, edgeStates, numEdges);
    memcpy(dbgTargetEdges, edgeStates, numEdges);
    hasDbgTarget = true;

    // Determine target remaining clues based on difficulty
    double keepRatio = 0.52;
    if (strcmp(difficulty, "medium") == 0) keepRatio = 0.42;
    else if (strcmp(difficulty, "hard") == 0) keepRatio = 0.22;
    else if (strcmp(difficulty, "expert") == 0) keepRatio = 0.0;

    int totalCells = rows * cols;
    int targetKeepCount = (int)(totalCells * keepRatio);
    
    // Group cells into 180-degree rotationally symmetric pairs
    typedef struct {
        int cellA;
        int cellB;
        int priority;
    } CellPair;
    
    static CellPair pairs[MAX_CELLS];
    int pairCount = 0;
    static bool paired[MAX_CELLS];
    memset(paired, 0, sizeof(paired));
    
    for (int i = 0; i < totalCells; i++) {
        if (paired[i]) continue;
        int r = i / cols;
        int c = i % cols;
        int symIdx = (rows - 1 - r) * cols + (cols - 1 - c);
        
        pairs[pairCount].cellA = i;
        pairs[pairCount].cellB = symIdx;
        paired[i] = true;
        paired[symIdx] = true;
        
        // Calculate priority
        int valA = clues[i];
        int valB = clues[symIdx];
        
        if (valA == 3 || valB == 3) {
            pairs[pairCount].priority = 2; // Keep 3 (check last)
        } else if (valA == 0 || valB == 0) {
            pairs[pairCount].priority = 2; // Keep 0 (check last)
        } else {
            pairs[pairCount].priority = 0; // Hide 1 and 2 first
        }
        pairCount++;
    }
    
    // Shuffle pairs first
    for (int i = pairCount - 1; i > 0; i--) {
        int j = rand() % (i + 1);
        CellPair temp = pairs[i];
        pairs[i] = pairs[j];
        pairs[j] = temp;
    }
    
    // Sort pairs by priority ascending (0, then 1, then 2)
    for (int i = 0; i < pairCount - 1; i++) {
        for (int j = i + 1; j < pairCount; j++) {
            if (pairs[j].priority < pairs[i].priority) {
                CellPair temp = pairs[i];
                pairs[i] = pairs[j];
                pairs[j] = temp;
            }
        }
    }

    int currentClueCount = 0;
    for (int i = 0; i < totalCells; i++) {
        if (clues[i] != -1) currentClueCount++;
    }

    solvabilityChecks = 0;
    fastPathCount = 0;
    printf("[C Generator] Starting symmetric minimization. Total cells: %d, Initial clues: %d, Target: %d\n", 
           totalCells, currentClueCount, targetKeepCount);
    
    // Check initial board solvability before any clue removal
    initSolvable = checkSolvability(difficulty);
    printf("Initial Board Solvability check: %d\n", initSolvable);

    // Pass 1: Prioritize removing specific clues based on difficulty
    if (strcmp(difficulty, "hard") == 0 || strcmp(difficulty, "expert") == 0) {
        for (int i = 0; i < pairCount; i++) {
            if (currentClueCount <= targetKeepCount) break;
            int cellA = pairs[i].cellA;
            int cellB = pairs[i].cellB;
            int8_t valA = clues[cellA];
            int8_t valB = clues[cellB];
            if (valA == -1 && valB == -1) continue;
            
            if (strcmp(difficulty, "hard") == 0) {
                // Hard: prioritize '0'
                if (valA != 0 && valB != 0) continue;
            } else {
                // Expert: prioritize '0' and '3' to reduce their frequency
                bool has0or3 = (valA == 0 || valA == 3 || valB == 0 || valB == 3);
                if (!has0or3) continue;
            }
            
            clues[cellA] = -1;
            clues[cellB] = -1;
            int removed = (cellA == cellB) ? 1 : 2;
            currentClueCount -= removed;
            if (!checkSolvability(difficulty)) {
                clues[cellA] = valA;
                clues[cellB] = valB;
                currentClueCount += removed;
            } else {
                pairs[i].cellA = -1; // Mark as processed
            }
        }
    }

    // Pass 2: General removal
    for (int i = 0; i < pairCount; i++) {
        if (currentClueCount <= targetKeepCount) break;

        int cellA = pairs[i].cellA;
        if (cellA == -1) continue; // Skip if removed in Pass 1
        int cellB = pairs[i].cellB;
        
        int8_t valA = clues[cellA];
        int8_t valB = clues[cellB];
        
        if (valA == -1 && valB == -1) continue;

        if (strcmp(difficulty, "easy") == 0 && (valA == 3 || valB == 3) && ((double)rand() / RAND_MAX) < 0.8) {
            continue;
        }

        // Try removing this pair
        clues[cellA] = -1;
        clues[cellB] = -1;
        int removed = (cellA == cellB) ? 1 : 2;
        currentClueCount -= removed;

        if (!checkSolvability(difficulty)) {
            // Restore clues if uniqueness/solvability is lost
            clues[cellA] = valA;
            clues[cellB] = valB;
            currentClueCount += removed;
        }

        if (solvabilityChecks % 10 == 0) {
            printf("[C Generator] Progress: Checked %d/%d pairs | Clues remaining: %d | FastPath: %d | Timeouts: %d\n",
                   solvabilityChecks, pairCount, currentClueCount, fastPathCount, debugTimeoutCount);
#ifdef __EMSCRIPTEN__
            EM_ASM({
                if (typeof self !== 'undefined' && typeof self.reportProgress === 'function') {
                    self.reportProgress($0, $1);
                }
            }, solvabilityChecks, pairCount);
#endif
        }
    }

    printf("[C Generator] Finished symmetric minimization! Final clues remaining: %d/%d (%d%%) | FastPath: %d/%d checks\n", 
           currentClueCount, totalCells, (currentClueCount * 100) / totalCells, fastPathCount, solvabilityChecks);

#ifdef __EMSCRIPTEN__
    EM_ASM({
        if (typeof self !== 'undefined' && typeof self.reportProgress === 'function') {
            self.reportProgress($0, $1);
        }
    }, pairCount, pairCount);
#endif

    // Debug symmetry check
    int asymmetryCount = 0;
    for (int i = 0; i < totalCells; i++) {
        int r = i / cols;
        int c = i % cols;
        int symIdx = (rows - 1 - r) * cols + (cols - 1 - c);
        
        bool hasA = (clues[i] != -1);
        bool hasB = (clues[symIdx] != -1);
        if (hasA != hasB) {
            asymmetryCount++;
            printf("[C Debug] Asymmetry detected at cell %d (%d,%d) vs %d (%d,%d) | clues: %d vs %d\n",
                   i, r, c, symIdx, rows - 1 - r, cols - 1 - c, clues[i], clues[symIdx]);
        }
    }
    if (asymmetryCount > 0) {
        printf("[C Debug] TOTAL ASYMMETRIC CELLS: %d / %d\n", asymmetryCount, totalCells);
    } else {
        printf("[C Debug] Perfect 180-degree symmetry confirmed!\n");
    }

    // Finalize: Restore the original target solved loop into edgeStates
    memcpy(edgeStates, targetEdgeStates, numEdges);
    memset(genCells, 0, sizeof(genCells));
}

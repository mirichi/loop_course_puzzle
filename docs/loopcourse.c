#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>
#include <math.h>

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
static inline int getHEdgeIndex(int r, int c) {
    if (r < 0 || r > rows || c < 0 || c >= cols) return -1;
    return r * cols + c;
}

static inline int getVEdgeIndex(int r, int c) {
    if (r < 0 || r >= rows || c < 0 || c > cols) return -1;
    return numH + r * (cols + 1) + c;
}

static inline void getCellEdges(int r, int c, int* outEdges) {
    outEdges[0] = r * cols + c;                         // top
    outEdges[1] = numH + r * (cols + 1) + (c + 1);      // right
    outEdges[2] = (r + 1) * cols + c;                     // bottom
    outEdges[3] = numH + r * (cols + 1) + c;            // left
}

static inline int getDotEdges(int r, int c, int* outEdges) {
    int count = 0;
    if (r > 0) outEdges[count++] = numH + (r - 1) * (cols + 1) + c;     // Up
    if (r < rows) outEdges[count++] = numH + r * (cols + 1) + c;        // Down
    if (c > 0) outEdges[count++] = r * cols + (c - 1);                  // Left
    if (c < cols) outEdges[count++] = r * cols + c;                     // Right
    return count;
}

static inline bool setEdgeState(int edgeIdx, int8_t state) {
    if (edgeStates[edgeIdx] == state) return true; // Already set to this state
    if (edgeStates[edgeIdx] != 0) return false;    // Contradiction: edge is already determined to a different state
    

    
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

// LOGICAL DEDUCTION ENGINE - INCREMENTAL PASS (AC-3 local constraint propagation)
static inline bool deductIncremental() {
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

        double fillRatioMin = 0.72;
        double fillRatioMax = 0.87;
        if (totalCells <= 36) {
            fillRatioMin = 0.40;
            fillRatioMax = 0.52;
        } else if (totalCells <= 64) {
            fillRatioMin = 0.48;
            fillRatioMax = 0.60;
        } else if (totalCells <= 144) {
            fillRatioMin = 0.58;
            fillRatioMax = 0.70;
        }

        int targetInsideCount = (int)(totalCells * (fillRatioMin + ((double)rand() / RAND_MAX) * (fillRatioMax - fillRatioMin)));
        int insideCount = 1;

        int failedAttempts = 0;
        int maxFailedAttempts = 300;
        int dr[] = {-1, 1, 0, 0};
        int dc[] = {0, 0, -1, 1};

        bool shouldBreakOutside = (totalCells >= 100);

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
                            double borderPenalty = (totalCells <= 64 && isBorder) ? 0.35 : 1.0;

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
    int maxSteps = 0;
    if (strcmp(difficulty, "easy") == 0) {
        maxSteps = 0;
    } else {
        int totalCells = rows * cols;
        if (totalCells > 150) {
            if (strcmp(difficulty, "medium") == 0) maxSteps = 25;
            else if (strcmp(difficulty, "hard") == 0) maxSteps = 600;
            else if (strcmp(difficulty, "expert") == 0) maxSteps = 1500;
            else maxSteps = 500;
        } else {
            if (strcmp(difficulty, "medium") == 0) maxSteps = 12;
            else if (strcmp(difficulty, "hard") == 0) maxSteps = 500;
            else if (strcmp(difficulty, "expert") == 0) maxSteps = 1000;
            else maxSteps = 300;
        }
    }

    // Backup current edgeStates before solving
    static int8_t origEdges[MAX_EDGES];
    memcpy(origEdges, edgeStates, numEdges);

    // Try pure logical deduction first (extremely fast, under 0.1ms)
    // If pure deduction determines all edges and satisfies all constraints,
    // the solution is unique, and we can skip backtracking completely!
    memset(edgeStates, 0, numEdges);
    bool deductSuccess = deduct();
    bool solvedSuccess = isSolved();
    bool allDecided = true;
    for (int i = 0; i < numEdges; i++) {
        if (edgeStates[i] == 0) {
            allDecided = false;
            break;
        }
    }
    
    // Print first few checks to avoid flooding output
    static int debugPrintCount = 0;
    if (debugPrintCount < 5) {
        printf("Debug Solvability: deduct=%d, solved=%d, allDecided=%d\n", deductSuccess, solvedSuccess, allDecided);
        debugPrintCount++;
    }

    if (deductSuccess && solvedSuccess && allDecided) {
        fastPathCount++;
        memcpy(edgeStates, origEdges, numEdges); // restore original
        return true;
    }

    if (maxSteps == 0) {
        memcpy(edgeStates, origEdges, numEdges); // restore original
        debugContradictionCount++;
        return false;
    }

    // Fallback to backtrack solver
    memset(edgeStates, 0, numEdges);
    int solutions = solve_puzzle_wasm(false, maxSteps);
    memcpy(edgeStates, origEdges, numEdges); // restore original

    if (solutions == -1) {
        debugTimeoutCount++;
    } else if (solutions != 1) {
        debugContradictionCount++;
    }

    return solutions == 1;
}

static int8_t sortTargetClues[MAX_CELLS];

static int compareCells(const void* a, const void* b) {
    int idxA = *(const int*)a;
    int idxB = *(const int*)b;
    int valA = sortTargetClues[idxA];
    int valB = sortTargetClues[idxB];
    int pA = (valA == 0) ? 0 : ((valA == 3) ? 2 : 1);
    int pB = (valB == 0) ? 0 : ((valB == 3) ? 2 : 1);
    return pA - pB;
}

// FULL MINIMIZATION ENGINE IN C (TOP-DOWN)
EMSCRIPTEN_KEEPALIVE
void generate_puzzle_wasm(const char* difficulty) {
    debugTimeoutCount = 0;
    debugContradictionCount = 0;

    // 1. Generate a random solved loop and calculate target clues
    generateRandomLoop();
    calculateClues();

    // Store target loop and clues
    static int8_t targetEdgeStates[MAX_EDGES];
    memcpy(targetEdgeStates, edgeStates, numEdges);
    memcpy(dbgTargetEdges, edgeStates, numEdges);
    hasDbgTarget = true;
    memcpy(sortTargetClues, clues, rows * cols);

    // Create a list of cell indices
    static int shuffledCells[MAX_CELLS];
    int totalCells = rows * cols;
    for (int i = 0; i < totalCells; i++) {
        shuffledCells[i] = i;
    }

    // Shuffle first for random order within same priority groups
    for (int i = totalCells - 1; i > 0; i--) {
        int j = rand() % (i + 1);
        int temp = shuffledCells[i];
        shuffledCells[i] = shuffledCells[j];
        shuffledCells[j] = temp;
    }

    // Sort by priority (0 first, then 1 & 2, then 3 last)
    qsort(shuffledCells, totalCells, sizeof(int), compareCells);

    // Determine target remaining clues based on difficulty
    double keepRatio = 0.52;
    if (strcmp(difficulty, "medium") == 0) keepRatio = 0.42;
    else if (strcmp(difficulty, "hard") == 0) keepRatio = 0.22;
    else if (strcmp(difficulty, "expert") == 0) keepRatio = 0.15;

    int targetKeepCount = (int)(totalCells * keepRatio);
    int currentClueCount = 0;
    for (int i = 0; i < totalCells; i++) {
        if (clues[i] != -1) currentClueCount++;
    }

    // TOP-DOWN MINIMIZATION: Use direct individual minimization (Pass 3) to prevent chunk rollback penalties.
    static int remainingCells[MAX_CELLS];
    int finalRemainingCount = 0;
    for (int i = 0; i < totalCells; i++) {
        int cellIdx = shuffledCells[i];
        if (clues[cellIdx] != -1) {
            remainingCells[finalRemainingCount++] = cellIdx;
        }
    }

    solvabilityChecks = 0;
    fastPathCount = 0;
    printf("[C Generator] Starting minimization. Total cells: %d, Initial clues: %d, Target: %d\n", 
           totalCells, currentClueCount, targetKeepCount);
    
    // Check initial board solvability before any clue removal
    bool initSolvable = checkSolvability(difficulty);
    printf("Initial Board Solvability check: %d\n", initSolvable);

    for (int i = 0; i < finalRemainingCount; i++) {
        if (currentClueCount <= targetKeepCount) break;

        int cellIdx = remainingCells[i];
        int8_t val = clues[cellIdx];
        if (val == -1) continue;

        if (strcmp(difficulty, "easy") == 0 && val == 3 && ((double)rand() / RAND_MAX) < 0.8) {
            continue;
        }

        // Try removing this clue
        clues[cellIdx] = -1;
        currentClueCount--;

        if (!checkSolvability(difficulty)) {
            // Restore clue if uniqueness is lost
            clues[cellIdx] = val;
            currentClueCount++;
        }

        if (solvabilityChecks % 50 == 0) {
            printf("[C Generator] Progress: Checked %d/%d cells | Clues remaining: %d | FastPath: %d | Timeouts: %d | Contradictions: %d\n",
                   solvabilityChecks, finalRemainingCount, currentClueCount, fastPathCount, debugTimeoutCount, debugContradictionCount);
        }
    }

    printf("[C Generator] Finished minimization! Final clues remaining: %d/%d (%d%%) | FastPath: %d/%d checks\n", 
           currentClueCount, totalCells, (currentClueCount * 100) / totalCells, fastPathCount, solvabilityChecks);

    // Finalize: Restore the original target solved loop into edgeStates
    memcpy(edgeStates, targetEdgeStates, numEdges);
    memset(genCells, 0, sizeof(genCells));
}

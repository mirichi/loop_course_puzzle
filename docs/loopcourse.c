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

// Feature Toggles for Benchmarking
bool enableAdvancedAC3 = true;
bool restrictLogicToLocal = false;


// pre-allocated stack for backtracking search to avoid constant allocations
#define MAX_BACKTRACK_DEPTH 200
static int8_t backupStack[MAX_BACKTRACK_DEPTH][MAX_EDGES];
static int8_t backupAfterDeductStack[MAX_BACKTRACK_DEPTH][MAX_EDGES];


// Graph adjacency list arrays for loop connection tracing (avoids allocations)
static int adj[MAX_DOTS][4];
static int adjCount[MAX_DOTS];
static bool visitedDots[MAX_DOTS];

// GF(2) Area Parity Solver memory
#define MAX_GF2_EQS 3500
#define MAX_GF2_VARS 3500
#define MAX_GF2_WORDS ((MAX_GF2_VARS + 63) / 64)

static uint64_t global_gf2_matrix[MAX_GF2_EQS][MAX_GF2_WORDS];
static uint8_t global_gf2_constants[MAX_GF2_EQS];
static int global_gf2_pivot[MAX_GF2_EQS];
static int global_gf2_num_eqs;
static int global_gf2_num_vars;
static int global_gf2_words;

static int gf2_update_queue[MAX_EDGES];
static int gf2_queue_head = 0;
static int gf2_queue_tail = 0;

static uint64_t backupStackGF2Matrix[MAX_BACKTRACK_DEPTH][MAX_GF2_EQS][MAX_GF2_WORDS];
static uint8_t backupStackGF2Constants[MAX_BACKTRACK_DEPTH][MAX_GF2_EQS];
static int backupStackGF2Pivot[MAX_BACKTRACK_DEPTH][MAX_GF2_EQS];

static uint64_t backupAfterDeductStackGF2Matrix[MAX_BACKTRACK_DEPTH][MAX_GF2_EQS][MAX_GF2_WORDS];
static uint8_t backupAfterDeductStackGF2Constants[MAX_BACKTRACK_DEPTH][MAX_GF2_EQS];
static int backupAfterDeductStackGF2Pivot[MAX_BACKTRACK_DEPTH][MAX_GF2_EQS];

static uint64_t check_gf2_matrix_backup[MAX_GF2_EQS][MAX_GF2_WORDS];
static uint8_t check_gf2_constants_backup[MAX_GF2_EQS];
static int check_gf2_pivot_backup[MAX_GF2_EQS];

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

// AC-3 Dirty Stack arrays
static int cellStack[MAX_CELLS * 4];
static int cellStackTop = 0;
static bool cellInStack[MAX_CELLS];

static int dotStack[MAX_DOTS * 4];
static int dotStackTop = 0;
static bool dotInStack[MAX_DOTS];

static inline void pushCell(int r, int c) {
    if (r < 0 || r >= rows || c < 0 || c >= cols) return;
    int idx = r * cols + c;
    if (clues[idx] == -1) return; // Only process cells with clues
    if (!cellInStack[idx]) {
        cellStack[cellStackTop++] = idx;
        cellInStack[idx] = true;
    }
}

static inline int popCell() {
    if (cellStackTop == 0) return -1;
    int idx = cellStack[--cellStackTop];
    cellInStack[idx] = false;
    return idx;
}

static inline void pushDot(int r, int c) {
    if (r < 0 || r > rows || c < 0 || c > cols) return;
    int idx = r * (cols + 1) + c;
    if (!dotInStack[idx]) {
        dotStack[dotStackTop++] = idx;
        dotInStack[idx] = true;
    }
}

static inline int popDot() {
    if (dotStackTop == 0) return -1;
    int idx = dotStack[--dotStackTop];
    dotInStack[idx] = false;
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

void init_lut();
void init_lut1x2();
bool applyLUT();

// API functions
EMSCRIPTEN_KEEPALIVE
void init_grid(int r, int c) {
    init_lut();
    init_lut1x2();
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

static inline int8_t getEdgeState(int edgeIdx) {
    if (edgeIdx < 0 || edgeIdx >= numEdges) return -1;
    return edgeStates[edgeIdx];
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
    // Local stack propagation
    if (edgeIdx < numH) {
        int r = edgeIdx / cols;
        int c = edgeIdx % cols;
        pushCell(r - 1, c);
        pushCell(r, c);
        pushDot(r, c);
        pushDot(r, c + 1);
    } else {
        int vIdx = edgeIdx - numH;
        int r = vIdx / (cols + 1);
        int c = vIdx % (cols + 1);
        pushCell(r, c - 1);
        pushCell(r, c);
        pushDot(r, c);
        pushDot(r + 1, c);
    }
    
    gf2_update_queue[gf2_queue_tail++] = edgeIdx;
    
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

// AC-3 Stack Utility to reset state on backtrack rollback
static inline void clearStacks() {
    cellStackTop = 0;
    memset(cellInStack, 0, sizeof(cellInStack));
    
    dotStackTop = 0;
    memset(dotInStack, 0, sizeof(dotInStack));
}

static inline int getSafeEdgeState(int idx) {
    return idx == -1 ? -1 : edgeStates[idx];
}

// --- NEW 2-3 CORNER LOGIC ---
static inline bool check23CornerLogic(int r, int c) {
    if (!enableAdvancedAC3) return true;
    int clue = clues[r * cols + c];
    if (clue != 2) return true;

    // Right adjacent 3
    if (c + 1 < cols && clues[r * cols + (c + 1)] == 3) {
        // Top-Left corner of 2: dot(r, c)
        if (getSafeEdgeState(getVEdgeIndex(r - 1, c)) == -1 && 
            getSafeEdgeState(getHEdgeIndex(r, c - 1)) == -1) {
            if (!setEdgeState(getHEdgeIndex(r, c + 1), 1)) return false;
            if (!setEdgeState(getVEdgeIndex(r, c + 2), 1)) return false;
        }
        // Bottom-Left corner of 2: dot(r+1, c)
        if (getSafeEdgeState(getVEdgeIndex(r + 1, c)) == -1 && 
            getSafeEdgeState(getHEdgeIndex(r + 1, c - 1)) == -1) {
            if (!setEdgeState(getHEdgeIndex(r + 1, c + 1), 1)) return false;
            if (!setEdgeState(getVEdgeIndex(r, c + 2), 1)) return false;
        }
    }
    // Left adjacent 3
    if (c - 1 >= 0 && clues[r * cols + (c - 1)] == 3) {
        // Top-Right corner of 2: dot(r, c+1)
        if (getSafeEdgeState(getVEdgeIndex(r - 1, c + 1)) == -1 && 
            getSafeEdgeState(getHEdgeIndex(r, c + 1)) == -1) {
            if (!setEdgeState(getHEdgeIndex(r, c - 1), 1)) return false;
            if (!setEdgeState(getVEdgeIndex(r, c - 1), 1)) return false;
        }
        // Bottom-Right corner of 2: dot(r+1, c+1)
        if (getSafeEdgeState(getVEdgeIndex(r + 1, c + 1)) == -1 && 
            getSafeEdgeState(getHEdgeIndex(r + 1, c + 1)) == -1) {
            if (!setEdgeState(getHEdgeIndex(r + 1, c - 1), 1)) return false;
            if (!setEdgeState(getVEdgeIndex(r, c - 1), 1)) return false;
        }
    }
    // Bottom adjacent 3
    if (r + 1 < rows && clues[(r + 1) * cols + c] == 3) {
        // Top-Left corner of 2: dot(r, c)
        if (getSafeEdgeState(getVEdgeIndex(r - 1, c)) == -1 && 
            getSafeEdgeState(getHEdgeIndex(r, c - 1)) == -1) {
            if (!setEdgeState(getVEdgeIndex(r + 1, c), 1)) return false;
            if (!setEdgeState(getHEdgeIndex(r + 2, c), 1)) return false;
        }
        // Top-Right corner of 2: dot(r, c+1)
        if (getSafeEdgeState(getVEdgeIndex(r - 1, c + 1)) == -1 && 
            getSafeEdgeState(getHEdgeIndex(r, c + 1)) == -1) {
            if (!setEdgeState(getVEdgeIndex(r + 1, c + 1), 1)) return false;
            if (!setEdgeState(getHEdgeIndex(r + 2, c), 1)) return false;
        }
    }
    // Top adjacent 3
    if (r - 1 >= 0 && clues[(r - 1) * cols + c] == 3) {
        // Bottom-Left corner of 2: dot(r+1, c)
        if (getSafeEdgeState(getVEdgeIndex(r + 1, c)) == -1 && 
            getSafeEdgeState(getHEdgeIndex(r + 1, c - 1)) == -1) {
            if (!setEdgeState(getVEdgeIndex(r - 1, c), 1)) return false;
            if (!setEdgeState(getHEdgeIndex(r - 1, c), 1)) return false;
        }
        // Bottom-Right corner of 2: dot(r+1, c+1)
        if (getSafeEdgeState(getVEdgeIndex(r + 1, c + 1)) == -1 && 
            getSafeEdgeState(getHEdgeIndex(r + 1, c + 1)) == -1) {
            if (!setEdgeState(getVEdgeIndex(r - 1, c + 1), 1)) return false;
            if (!setEdgeState(getHEdgeIndex(r - 1, c), 1)) return false;
        }
    }
    return true;
}

static inline bool check22CornerLogic(int r, int c) {
    if (!enableAdvancedAC3) return true;
    int clue = clues[r * cols + c];
    if (clue != 2) return true;

    // Right adjacent 2
    if (c + 1 < cols && clues[r * cols + (c + 1)] == 2) {
        // Bottom outer corners: (r+1, c) and (r+1, c+2)
        if (getSafeEdgeState(getVEdgeIndex(r + 1, c)) == -1 && 
            getSafeEdgeState(getHEdgeIndex(r + 1, c - 1)) == -1 &&
            getSafeEdgeState(getVEdgeIndex(r + 1, c + 2)) == -1 &&
            getSafeEdgeState(getHEdgeIndex(r + 1, c + 2)) == -1) {
            
            if (!setEdgeState(getVEdgeIndex(r, c), 1)) return false;
            if (!setEdgeState(getHEdgeIndex(r + 1, c), 1)) return false;
            if (!setEdgeState(getVEdgeIndex(r, c + 2), 1)) return false;
            if (!setEdgeState(getHEdgeIndex(r + 1, c + 1), 1)) return false;
        }
        // Top outer corners: (r, c) and (r, c+2)
        if (getSafeEdgeState(getVEdgeIndex(r - 1, c)) == -1 && 
            getSafeEdgeState(getHEdgeIndex(r, c - 1)) == -1 &&
            getSafeEdgeState(getVEdgeIndex(r - 1, c + 2)) == -1 &&
            getSafeEdgeState(getHEdgeIndex(r, c + 2)) == -1) {
            
            if (!setEdgeState(getVEdgeIndex(r, c), 1)) return false;
            if (!setEdgeState(getHEdgeIndex(r, c), 1)) return false;
            if (!setEdgeState(getVEdgeIndex(r, c + 2), 1)) return false;
            if (!setEdgeState(getHEdgeIndex(r, c + 1), 1)) return false;
        }
    }
    // Bottom adjacent 2
    if (r + 1 < rows && clues[(r + 1) * cols + c] == 2) {
        // Left outer corners: (r, c) and (r+2, c)
        if (getSafeEdgeState(getVEdgeIndex(r - 1, c)) == -1 && 
            getSafeEdgeState(getHEdgeIndex(r, c - 1)) == -1 &&
            getSafeEdgeState(getVEdgeIndex(r + 2, c)) == -1 &&
            getSafeEdgeState(getHEdgeIndex(r + 2, c - 1)) == -1) {
            
            if (!setEdgeState(getHEdgeIndex(r, c), 1)) return false;
            if (!setEdgeState(getVEdgeIndex(r, c), 1)) return false;
            if (!setEdgeState(getHEdgeIndex(r + 2, c), 1)) return false;
            if (!setEdgeState(getVEdgeIndex(r + 1, c), 1)) return false;
        }
        // Right outer corners: (r, c+1) and (r+2, c+1)
        if (getSafeEdgeState(getVEdgeIndex(r - 1, c + 1)) == -1 && 
            getSafeEdgeState(getHEdgeIndex(r, c + 1)) == -1 &&
            getSafeEdgeState(getVEdgeIndex(r + 2, c + 1)) == -1 &&
            getSafeEdgeState(getHEdgeIndex(r + 2, c + 1)) == -1) {
            
            if (!setEdgeState(getHEdgeIndex(r, c), 1)) return false;
            if (!setEdgeState(getVEdgeIndex(r, c + 1), 1)) return false;
            if (!setEdgeState(getHEdgeIndex(r + 2, c), 1)) return false;
            if (!setEdgeState(getVEdgeIndex(r + 1, c + 1), 1)) return false;
        }
    }
    return true;
}

static void initGlobalGF2() {
    global_gf2_num_eqs = 0;
    global_gf2_num_vars = numEdges;
    global_gf2_words = (numEdges + 63) / 64;
    
    memset(global_gf2_matrix, 0, sizeof(global_gf2_matrix));
    memset(global_gf2_constants, 0, sizeof(global_gf2_constants));
    memset(global_gf2_pivot, -1, sizeof(global_gf2_pivot));
    
    // 1. Clue parity equations
    for (int r = 0; r < rows; r++) {
        for (int c = 0; c < cols; c++) {
            int clue = clues[r * cols + c];
            if (clue == -1) continue;
            
            int edges[4];
            getCellEdges(r, c, edges);
            int eq_idx = global_gf2_num_eqs++;
            for (int i = 0; i < 4; i++) {
                int e = edges[i];
                global_gf2_matrix[eq_idx][e / 64] |= (1ULL << (e % 64));
            }
            global_gf2_constants[eq_idx] = clue % 2;
        }
    }
    
    // 2. Dot parity equations
    for (int r = 0; r <= rows; r++) {
        for (int c = 0; c <= cols; c++) {
            int edges[4];
            int count = getDotEdges(r, c, edges);
            int eq_idx = global_gf2_num_eqs++;
            for (int i = 0; i < count; i++) {
                int e = edges[i];
                global_gf2_matrix[eq_idx][e / 64] |= (1ULL << (e % 64));
            }
            global_gf2_constants[eq_idx] = 0;
        }
    }
    
    // 3. Gaussian Elimination to RREF
    int pivot_row = 0;
    for (int c = 0; c < global_gf2_num_vars && pivot_row < global_gf2_num_eqs; c++) {
        int best_r = -1;
        for (int r = pivot_row; r < global_gf2_num_eqs; r++) {
            if (global_gf2_matrix[r][c / 64] & (1ULL << (c % 64))) {
                best_r = r;
                break;
            }
        }
        
        if (best_r == -1) continue;
        
        if (best_r != pivot_row) {
            for (int w = 0; w < global_gf2_words; w++) {
                uint64_t tmp = global_gf2_matrix[pivot_row][w];
                global_gf2_matrix[pivot_row][w] = global_gf2_matrix[best_r][w];
                global_gf2_matrix[best_r][w] = tmp;
            }
            uint8_t tmp_c = global_gf2_constants[pivot_row];
            global_gf2_constants[pivot_row] = global_gf2_constants[best_r];
            global_gf2_constants[best_r] = tmp_c;
        }
        
        global_gf2_pivot[pivot_row] = c;
        
        for (int r = 0; r < global_gf2_num_eqs; r++) {
            if (r != pivot_row) {
                if (global_gf2_matrix[r][c / 64] & (1ULL << (c % 64))) {
                    for (int w = 0; w < global_gf2_words; w++) {
                        global_gf2_matrix[r][w] ^= global_gf2_matrix[pivot_row][w];
                    }
                    global_gf2_constants[r] ^= global_gf2_constants[pivot_row];
                }
            }
        }
        pivot_row++;
    }
    
    gf2_queue_head = 0;
    gf2_queue_tail = 0;
}

static bool updateGlobalGF2(int e, int val) {
    bool row_modified[MAX_GF2_EQS] = {false};
    
    for (int r = 0; r < global_gf2_num_eqs; r++) {
        if (global_gf2_matrix[r][e / 64] & (1ULL << (e % 64))) {
            global_gf2_matrix[r][e / 64] &= ~(1ULL << (e % 64));
            global_gf2_constants[r] ^= val;
            row_modified[r] = true;
            
            if (global_gf2_pivot[r] == e) {
                int new_pivot = -1;
                for (int w = 0; w < global_gf2_words; w++) {
                    if (global_gf2_matrix[r][w] != 0) {
                        new_pivot = w * 64 + __builtin_ctzll(global_gf2_matrix[r][w]);
                        break;
                    }
                }
                global_gf2_pivot[r] = new_pivot;
                
                if (new_pivot != -1) {
                    for (int i = 0; i < global_gf2_num_eqs; i++) {
                        if (i != r && (global_gf2_matrix[i][new_pivot / 64] & (1ULL << (new_pivot % 64)))) {
                            for (int w = 0; w < global_gf2_words; w++) {
                                global_gf2_matrix[i][w] ^= global_gf2_matrix[r][w];
                            }
                            global_gf2_constants[i] ^= global_gf2_constants[r];
                            row_modified[i] = true;
                        }
                    }
                } else {
                    if (global_gf2_constants[r] != 0) {
                        return false;
                    }
                }
            }
        }
    }
    
    for (int r = 0; r < global_gf2_num_eqs; r++) {
        if (row_modified[r] && global_gf2_pivot[r] != -1) {
            int popcount = 0;
            for (int w = 0; w < global_gf2_words; w++) {
                popcount += __builtin_popcountll(global_gf2_matrix[r][w]);
            }
            if (popcount == 1) {
                int p = global_gf2_pivot[r];
                int state = (global_gf2_constants[r] == 1) ? 1 : -1;
                if (edgeStates[p] == 0) {
                    if (!setEdgeState(p, state)) return false;
                } else if (edgeStates[p] != state) {
                    return false;
                }
            } else if (popcount == 0) {
                if (global_gf2_constants[r] != 0) return false;
                global_gf2_pivot[r] = -1;
            }
        }
    }
    return true;
}

#include "lut_module.h"
#include "lut1x2_module.h"

static bool applyStaticRules() {
    initGlobalGF2();
    dbgSource = "static_rules";

    for (int r = 0; r < rows; r++) {
        for (int c = 0; c < cols; c++) {
            int clue = clues[r * cols + c];
            if (clue == -1) continue;
            
            // Rule 1: Clue 0 (All edges are crosses)
            if (clue == 0) {
                if (!setEdgeState(getHEdgeIndex(r, c), -1)) return false;
                if (!setEdgeState(getVEdgeIndex(r, c), -1)) return false;
                if (!setEdgeState(getHEdgeIndex(r + 1, c), -1)) return false;
                if (!setEdgeState(getVEdgeIndex(r, c + 1), -1)) return false;
                continue;
            }
            
            // Rule 2.1: Orthogonally Adjacent 3-3 Cells
            if (clue == 3) {
                if (c + 1 < cols && clues[r * cols + (c + 1)] == 3) {
                    int shared = getVEdgeIndex(r, c + 1);
                    int outerL = getVEdgeIndex(r, c);
                    int outerR = getVEdgeIndex(r, c + 2);
                    if (!setEdgeState(shared, 1)) return false;
                    if (!setEdgeState(outerL, 1)) return false;
                    if (!setEdgeState(outerR, 1)) return false;
                    
                    int above = getVEdgeIndex(r - 1, c + 1);
                    int below = getVEdgeIndex(r + 1, c + 1);
                    if (above != -1 && !setEdgeState(above, -1)) return false;
                    if (below != -1 && !setEdgeState(below, -1)) return false;
                    
                    // Rule 2.1b: 3-3 Orthogonal with adjacent 2
                    // Above left 3
                    if (r - 1 >= 0 && clues[(r - 1) * cols + c] == 2) {
                        if (!setEdgeState(getHEdgeIndex(r - 1, c), 1)) return false;
                        if (!setEdgeState(getHEdgeIndex(r, c - 1), -1)) return false;
                    }
                    // Above right 3
                    if (r - 1 >= 0 && clues[(r - 1) * cols + c + 1] == 2) {
                        if (!setEdgeState(getHEdgeIndex(r - 1, c + 1), 1)) return false;
                        if (!setEdgeState(getHEdgeIndex(r, c + 2), -1)) return false;
                    }
                    // Below left 3
                    if (r + 1 < rows && clues[(r + 1) * cols + c] == 2) {
                        if (!setEdgeState(getHEdgeIndex(r + 2, c), 1)) return false;
                        if (!setEdgeState(getHEdgeIndex(r + 1, c - 1), -1)) return false;
                    }
                    // Below right 3
                    if (r + 1 < rows && clues[(r + 1) * cols + c + 1] == 2) {
                        if (!setEdgeState(getHEdgeIndex(r + 2, c + 1), 1)) return false;
                        if (!setEdgeState(getHEdgeIndex(r + 1, c + 2), -1)) return false;
                    }
                }
                if (r + 1 < rows && clues[(r + 1) * cols + c] == 3) {
                    int shared = getHEdgeIndex(r + 1, c);
                    int outerT = getHEdgeIndex(r, c);
                    int outerB = getHEdgeIndex(r + 2, c);
                    if (!setEdgeState(shared, 1)) return false;
                    if (!setEdgeState(outerT, 1)) return false;
                    if (!setEdgeState(outerB, 1)) return false;
                    
                    int leftwards = getHEdgeIndex(r + 1, c - 1);
                    int rightwards = getHEdgeIndex(r + 1, c + 1);
                    if (leftwards != -1 && !setEdgeState(leftwards, -1)) return false;
                    if (rightwards != -1 && !setEdgeState(rightwards, -1)) return false;
                    
                    // Rule 2.1b: 3-3 Orthogonal with adjacent 2
                    // Left of top 3
                    if (c - 1 >= 0 && clues[r * cols + c - 1] == 2) {
                        if (!setEdgeState(getVEdgeIndex(r, c - 1), 1)) return false;
                        if (!setEdgeState(getVEdgeIndex(r - 1, c), -1)) return false;
                    }
                    // Left of bottom 3
                    if (c - 1 >= 0 && clues[(r + 1) * cols + c - 1] == 2) {
                        if (!setEdgeState(getVEdgeIndex(r + 1, c - 1), 1)) return false;
                        if (!setEdgeState(getVEdgeIndex(r + 2, c), -1)) return false;
                    }
                    // Right of top 3
                    if (c + 1 < cols && clues[r * cols + c + 1] == 2) {
                        if (!setEdgeState(getVEdgeIndex(r, c + 2), 1)) return false;
                        if (!setEdgeState(getVEdgeIndex(r - 1, c + 1), -1)) return false;
                    }
                    // Right of bottom 3
                    if (c + 1 < cols && clues[(r + 1) * cols + c + 1] == 2) {
                        if (!setEdgeState(getVEdgeIndex(r + 1, c + 2), 1)) return false;
                        if (!setEdgeState(getVEdgeIndex(r + 2, c + 1), -1)) return false;
                    }
                }
            }
            
            // Rule 2.1c: Clue 3 surrounded by two 1s forming a corner
            if (clue == 3) {
                // Top-Right Corner (1 at Top, 1 at Right)
                if (r - 1 >= 0 && c + 1 < cols && clues[(r - 1) * cols + c] == 1 && clues[r * cols + c + 1] == 1) {
                    if (!setEdgeState(getHEdgeIndex(r - 1, c), -1)) return false; // Top of Top 1
                    if (!setEdgeState(getVEdgeIndex(r - 1, c), -1)) return false; // Left of Top 1
                    if (!setEdgeState(getVEdgeIndex(r, c + 2), -1)) return false; // Right of Right 1
                    if (!setEdgeState(getHEdgeIndex(r + 1, c + 1), -1)) return false; // Bottom of Right 1
                }
                // Top-Left Corner (1 at Top, 1 at Left)
                if (r - 1 >= 0 && c - 1 >= 0 && clues[(r - 1) * cols + c] == 1 && clues[r * cols + c - 1] == 1) {
                    if (!setEdgeState(getHEdgeIndex(r - 1, c), -1)) return false; // Top of Top 1
                    if (!setEdgeState(getVEdgeIndex(r - 1, c + 1), -1)) return false; // Right of Top 1
                    if (!setEdgeState(getVEdgeIndex(r, c - 1), -1)) return false; // Left of Left 1
                    if (!setEdgeState(getHEdgeIndex(r + 1, c - 1), -1)) return false; // Bottom of Left 1
                }
                // Bottom-Left Corner (1 at Bottom, 1 at Left)
                if (r + 1 < rows && c - 1 >= 0 && clues[(r + 1) * cols + c] == 1 && clues[r * cols + c - 1] == 1) {
                    if (!setEdgeState(getHEdgeIndex(r + 2, c), -1)) return false; // Bottom of Bottom 1
                    if (!setEdgeState(getVEdgeIndex(r + 1, c + 1), -1)) return false; // Right of Bottom 1
                    if (!setEdgeState(getVEdgeIndex(r, c - 1), -1)) return false; // Left of Left 1
                    if (!setEdgeState(getHEdgeIndex(r, c - 1), -1)) return false; // Top of Left 1
                }
                // Bottom-Right Corner (1 at Bottom, 1 at Right)
                if (r + 1 < rows && c + 1 < cols && clues[(r + 1) * cols + c] == 1 && clues[r * cols + c + 1] == 1) {
                    if (!setEdgeState(getHEdgeIndex(r + 2, c), -1)) return false; // Bottom of Bottom 1
                    if (!setEdgeState(getVEdgeIndex(r + 1, c), -1)) return false; // Left of Bottom 1
                    if (!setEdgeState(getVEdgeIndex(r, c + 2), -1)) return false; // Right of Right 1
                    if (!setEdgeState(getHEdgeIndex(r, c + 1), -1)) return false; // Top of Right 1
                }
            }
            
            // Rule 2.1d: 1 and 3 adjacent along the grid border
            if (clue == 3) {
                // Top border
                if (r == 0) {
                    if (c - 1 >= 0 && clues[0 * cols + c - 1] == 1) { // 1 is on the left
                        if (!setEdgeState(getHEdgeIndex(0, c), 1)) return false; // Top of 3
                        if (!setEdgeState(getVEdgeIndex(0, c - 1), -1)) return false; // Left of 1
                        if (!setEdgeState(getHEdgeIndex(1, c - 1), -1)) return false; // Bottom of 1
                    }
                    if (c + 1 < cols && clues[0 * cols + c + 1] == 1) { // 1 is on the right
                        if (!setEdgeState(getHEdgeIndex(0, c), 1)) return false; // Top of 3
                        if (!setEdgeState(getVEdgeIndex(0, c + 2), -1)) return false; // Right of 1
                        if (!setEdgeState(getHEdgeIndex(1, c + 1), -1)) return false; // Bottom of 1
                    }
                }
                // Bottom border
                if (r == rows - 1) {
                    if (c - 1 >= 0 && clues[(rows - 1) * cols + c - 1] == 1) { // 1 is on the left
                        if (!setEdgeState(getHEdgeIndex(rows, c), 1)) return false; // Bottom of 3
                        if (!setEdgeState(getVEdgeIndex(rows - 1, c - 1), -1)) return false; // Left of 1
                        if (!setEdgeState(getHEdgeIndex(rows - 1, c - 1), -1)) return false; // Top of 1
                    }
                    if (c + 1 < cols && clues[(rows - 1) * cols + c + 1] == 1) { // 1 is on the right
                        if (!setEdgeState(getHEdgeIndex(rows, c), 1)) return false; // Bottom of 3
                        if (!setEdgeState(getVEdgeIndex(rows - 1, c + 2), -1)) return false; // Right of 1
                        if (!setEdgeState(getHEdgeIndex(rows - 1, c + 1), -1)) return false; // Top of 1
                    }
                }
                // Left border
                if (c == 0) {
                    if (r - 1 >= 0 && clues[(r - 1) * cols + 0] == 1) { // 1 is above
                        if (!setEdgeState(getVEdgeIndex(r, 0), 1)) return false; // Left of 3
                        if (!setEdgeState(getHEdgeIndex(r - 1, 0), -1)) return false; // Top of 1
                        if (!setEdgeState(getVEdgeIndex(r - 1, 1), -1)) return false; // Right of 1
                    }
                    if (r + 1 < rows && clues[(r + 1) * cols + 0] == 1) { // 1 is below
                        if (!setEdgeState(getVEdgeIndex(r, 0), 1)) return false; // Left of 3
                        if (!setEdgeState(getHEdgeIndex(r + 2, 0), -1)) return false; // Bottom of 1
                        if (!setEdgeState(getVEdgeIndex(r + 1, 1), -1)) return false; // Right of 1
                    }
                }
                // Right border
                if (c == cols - 1) {
                    if (r - 1 >= 0 && clues[(r - 1) * cols + cols - 1] == 1) { // 1 is above
                        if (!setEdgeState(getVEdgeIndex(r, cols), 1)) return false; // Right of 3
                        if (!setEdgeState(getHEdgeIndex(r - 1, cols - 1), -1)) return false; // Top of 1
                        if (!setEdgeState(getVEdgeIndex(r - 1, cols - 1), -1)) return false; // Left of 1
                    }
                    if (r + 1 < rows && clues[(r + 1) * cols + cols - 1] == 1) { // 1 is below
                        if (!setEdgeState(getVEdgeIndex(r, cols), 1)) return false; // Right of 3
                        if (!setEdgeState(getHEdgeIndex(r + 2, cols - 1), -1)) return false; // Bottom of 1
                        if (!setEdgeState(getVEdgeIndex(r + 1, cols - 1), -1)) return false; // Left of 1
                    }
                }
            }
            
            // Rule 2.1e: 3-2-3 along the grid border
            if (clue == 2 && rows * cols > 3) {
                // Top border
                if (r == 0 && c - 1 >= 0 && c + 1 < cols && clues[0 * cols + c - 1] == 3 && clues[0 * cols + c + 1] == 3) {
                    if (!setEdgeState(getHEdgeIndex(1, c), -1)) return false; // Bottom of 2
                }
                // Bottom border
                if (r == rows - 1 && c - 1 >= 0 && c + 1 < cols && clues[(rows - 1) * cols + c - 1] == 3 && clues[(rows - 1) * cols + c + 1] == 3) {
                    if (!setEdgeState(getHEdgeIndex(rows - 1, c), -1)) return false; // Top of 2
                }
                // Left border
                if (c == 0 && r - 1 >= 0 && r + 1 < rows && clues[(r - 1) * cols + 0] == 3 && clues[(r + 1) * cols + 0] == 3) {
                    if (!setEdgeState(getVEdgeIndex(r, 1), -1)) return false; // Right of 2
                }
                // Right border
                if (c == cols - 1 && r - 1 >= 0 && r + 1 < rows && clues[(r - 1) * cols + cols - 1] == 3 && clues[(r + 1) * cols + cols - 1] == 3) {
                    if (!setEdgeState(getVEdgeIndex(r, cols - 1), -1)) return false; // Left of 2
                }
            }
            
            // Rule 2.1f: 2 surrounded by three 1s
            if (clue == 2) {
                // Top, Left, Right are 1s -> Top of Top 1 is X
                if (r - 1 >= 0 && c - 1 >= 0 && c + 1 < cols && 
                    clues[(r - 1) * cols + c] == 1 && clues[r * cols + c - 1] == 1 && clues[r * cols + c + 1] == 1) {
                    if (!setEdgeState(getHEdgeIndex(r - 1, c), -1)) return false;
                }
                // Bottom, Left, Right are 1s -> Bottom of Bottom 1 is X
                if (r + 1 < rows && c - 1 >= 0 && c + 1 < cols && 
                    clues[(r + 1) * cols + c] == 1 && clues[r * cols + c - 1] == 1 && clues[r * cols + c + 1] == 1) {
                    if (!setEdgeState(getHEdgeIndex(r + 2, c), -1)) return false;
                }
                // Left, Top, Bottom are 1s -> Left of Left 1 is X
                if (c - 1 >= 0 && r - 1 >= 0 && r + 1 < rows && 
                    clues[r * cols + c - 1] == 1 && clues[(r - 1) * cols + c] == 1 && clues[(r + 1) * cols + c] == 1) {
                    if (!setEdgeState(getVEdgeIndex(r, c - 1), -1)) return false;
                }
                // Right, Top, Bottom are 1s -> Right of Right 1 is X
                if (c + 1 < cols && r - 1 >= 0 && r + 1 < rows && 
                    clues[r * cols + c + 1] == 1 && clues[(r - 1) * cols + c] == 1 && clues[(r + 1) * cols + c] == 1) {
                    if (!setEdgeState(getVEdgeIndex(r, c + 2), -1)) return false;
                }
            }
            
            // Rule 2.1g: 1-1 adjacent along the grid border
            if (clue == 1) {
                // Horizontal adjacency (along Top or Bottom border)
                if (r == 0 || r == rows - 1) {
                    if (c + 1 < cols && clues[r * cols + c + 1] == 1) {
                        if (!setEdgeState(getVEdgeIndex(r, c + 1), -1)) return false; // Shared vertical edge
                    }
                }
                // Vertical adjacency (along Left or Right border)
                if (c == 0 || c == cols - 1) {
                    if (r + 1 < rows && clues[(r + 1) * cols + c] == 1) {
                        if (!setEdgeState(getHEdgeIndex(r + 1, c), -1)) return false; // Shared horizontal edge
                    }
                }
            }
            
            // Rule 2.2: Generalized Diagonal Chains (3-2...2-3 and 3-2...2-0)
            if (clue == 3) {
                int drs[] = {-1, -1, 1, 1};
                int dcs[] = {-1, 1, -1, 1};
                for (int i = 0; i < 4; i++) {
                    int dr = drs[i];
                    int dc = dcs[i];
                    int er = r + dr;
                    int ec = c + dc;
                    while (er >= 0 && er < rows && ec >= 0 && ec < cols && clues[er * cols + ec] == 2) {
                        er += dr;
                        ec += dc;
                    }
                    if (er >= 0 && er < rows && ec >= 0 && ec < cols) {
                        if (clues[er * cols + ec] == 3) {
                            // 3-2...2-3 Chain: Outer edges of the starting 3 are lines.
                            int startOuterH = (dr == 1) ? getHEdgeIndex(r, c) : getHEdgeIndex(r + 1, c);
                            int startOuterV = (dc == 1) ? getVEdgeIndex(r, c) : getVEdgeIndex(r, c + 1);
                            if (!setEdgeState(startOuterH, 1)) return false;
                            if (!setEdgeState(startOuterV, 1)) return false;
                            
                            // Set external edges at the corner to crosses
                            int cornerR = (dr == 1) ? r : r + 1;
                            int cornerC = (dc == 1) ? c : c + 1;
                            int extV = (dr == 1) ? getVEdgeIndex(r - 1, cornerC) : getVEdgeIndex(r + 1, cornerC);
                            int extH = (dc == 1) ? getHEdgeIndex(cornerR, c - 1) : getHEdgeIndex(cornerR, c + 1);
                            if (!setEdgeState(extV, -1)) return false;
                            if (!setEdgeState(extH, -1)) return false;
                        } else if (clues[er * cols + ec] == 0) {
                            // 3-2...2-0 Chain: Edges facing 0 are lines, edges facing 3 are crosses.
                            // For the 3:
                            int startInnerH = (dr == 1) ? getHEdgeIndex(r + 1, c) : getHEdgeIndex(r, c);
                            int startInnerV = (dc == 1) ? getVEdgeIndex(r, c + 1) : getVEdgeIndex(r, c);
                            if (!setEdgeState(startInnerH, 1)) return false;
                            if (!setEdgeState(startInnerV, 1)) return false;
                            
                            // For the 2s:
                            int tr = r + dr;
                            int tc = c + dc;
                            while (tr != er) {
                                // Edges facing 0 (inner) -> Lines
                                int innerH = (dr == 1) ? getHEdgeIndex(tr + 1, tc) : getHEdgeIndex(tr, tc);
                                int innerV = (dc == 1) ? getVEdgeIndex(tr, tc + 1) : getVEdgeIndex(tr, tc);
                                if (!setEdgeState(innerH, 1)) return false;
                                if (!setEdgeState(innerV, 1)) return false;
                                
                                // Edges facing 3 (outer) -> Crosses
                                int outerH = (dr == 1) ? getHEdgeIndex(tr, tc) : getHEdgeIndex(tr + 1, tc);
                                int outerV = (dc == 1) ? getVEdgeIndex(tr, tc) : getVEdgeIndex(tr, tc + 1);
                                if (!setEdgeState(outerH, -1)) return false;
                                if (!setEdgeState(outerV, -1)) return false;
                                
                                tr += dr;
                                tc += dc;
                            }
                        }
                    }
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
    
    // Rule 2.6: Clue 3, 1, 2 in Grid Corners
    // Top-Left
    int clueCorner = clues[0];
    if (clueCorner != -1) {
        if (clueCorner == 3) {
            if (!setEdgeState(getHEdgeIndex(0, 0), 1)) return false;
            if (!setEdgeState(getVEdgeIndex(0, 0), 1)) return false;
        } else if (clueCorner == 1) {
            if (!setEdgeState(getHEdgeIndex(0, 0), -1)) return false;
            if (!setEdgeState(getVEdgeIndex(0, 0), -1)) return false;
        } else if (clueCorner == 2) {
            if (cols > 1 && !setEdgeState(getHEdgeIndex(0, 1), 1)) return false;
            if (rows > 1 && !setEdgeState(getVEdgeIndex(1, 0), 1)) return false;
        }
    }
    // Top-Right
    clueCorner = clues[cols - 1];
    if (clueCorner != -1) {
        if (clueCorner == 3) {
            if (!setEdgeState(getHEdgeIndex(0, cols - 1), 1)) return false;
            if (!setEdgeState(getVEdgeIndex(0, cols), 1)) return false;
        } else if (clueCorner == 1) {
            if (!setEdgeState(getHEdgeIndex(0, cols - 1), -1)) return false;
            if (!setEdgeState(getVEdgeIndex(0, cols), -1)) return false;
        } else if (clueCorner == 2) {
            if (cols > 1 && !setEdgeState(getHEdgeIndex(0, cols - 2), 1)) return false;
            if (rows > 1 && !setEdgeState(getVEdgeIndex(1, cols), 1)) return false;
        }
    }
    // Bottom-Left
    clueCorner = clues[(rows - 1) * cols];
    if (clueCorner != -1) {
        if (clueCorner == 3) {
            if (!setEdgeState(getHEdgeIndex(rows, 0), 1)) return false;
            if (!setEdgeState(getVEdgeIndex(rows - 1, 0), 1)) return false;
        } else if (clueCorner == 1) {
            if (!setEdgeState(getHEdgeIndex(rows, 0), -1)) return false;
            if (!setEdgeState(getVEdgeIndex(rows - 1, 0), -1)) return false;
        } else if (clueCorner == 2) {
            if (cols > 1 && !setEdgeState(getHEdgeIndex(rows, 1), 1)) return false;
            if (rows > 1 && !setEdgeState(getVEdgeIndex(rows - 2, 0), 1)) return false;
        }
    }
    // Bottom-Right
    clueCorner = clues[(rows - 1) * cols + cols - 1];
    if (clueCorner != -1) {
        if (clueCorner == 3) {
            if (!setEdgeState(getHEdgeIndex(rows, cols - 1), 1)) return false;
            if (!setEdgeState(getVEdgeIndex(rows - 1, cols), 1)) return false;
        } else if (clueCorner == 1) {
            if (!setEdgeState(getHEdgeIndex(rows, cols - 1), -1)) return false;
            if (!setEdgeState(getVEdgeIndex(rows - 1, cols), -1)) return false;
        } else if (clueCorner == 2) {
            if (cols > 1 && !setEdgeState(getHEdgeIndex(rows, cols - 2), 1)) return false;
            if (rows > 1 && !setEdgeState(getVEdgeIndex(rows - 2, cols), 1)) return false;
        }
    }

    int afterStatic = 0;
    for(int i=0; i<numEdges; i++) if(edgeStates[i] != 0) afterStatic++;
    extern int staticRuleEdgesTotal;
    staticRuleEdgesTotal += afterStatic;

    if (!applyLUT()) return false;
    
    bool lut1x2_changed;
    do {
        lut1x2_changed = false;
        if (!applyLUT1x2(&lut1x2_changed)) return false;
    } while (lut1x2_changed);

    int afterLUT = 0;
    for(int i=0; i<numEdges; i++) if(edgeStates[i] != 0) afterLUT++;
    extern int lutEdgesTotal;
    lutEdgesTotal += (afterLUT - afterStatic);

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
        
        if (clue == 0) {
            return false;
        } else if (clue == 1) {
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
static inline int checkDiagonalChain(int startClue, int r, int c, int dr, int dc) {
    int curr_r = r + dr;
    int curr_c = c + dc;
    while (getClue(curr_r, curr_c) == 2) {
        curr_r += dr;
        curr_c += dc;
    }
    int clue = getClue(curr_r, curr_c);
    int result = 0;
    
    // Check SLE Contradiction (State B is impossible)
    if (clue == 0) {
        result |= 2;
    }
    
    // Check Zero-Line Contradiction (State A is impossible)
    if (clue == 3) {
        if (startClue == 3) {
            result |= 1;
        }
    } else if (clue == 1) {
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
        if (oppEdge1 != -1 && oppEdge2 != -1 && edgeStates[oppEdge1] == -1 && edgeStates[oppEdge2] == -1) {
            result |= 1;
        }
    }
    
    return result;
}

static inline bool checkDotBorderLogic(int r, int c) {
    int eT = (r > 0) ? getVEdgeIndex(r - 1, c) : -1;
    int eB = (r < rows) ? getVEdgeIndex(r, c) : -1;
    int eL = (c > 0) ? getHEdgeIndex(r, c - 1) : -1;
    int eR = (c < cols) ? getHEdgeIndex(r, c) : -1;

    int stateT = (eT != -1) ? edgeStates[eT] : -1;
    int stateB = (eB != -1) ? edgeStates[eB] : -1;
    int stateL = (eL != -1) ? edgeStates[eL] : -1;
    int stateR = (eR != -1) ? edgeStates[eR] : -1;

    // If Top is CROSS, evaluate Bottom edge (separates Bottom-Left and Bottom-Right cells)
    if (stateT == -1 && eB != -1) {
        int clueL = (c > 0 && r < rows) ? clues[r * cols + (c - 1)] : -1;
        int clueR = (c < cols && r < rows) ? clues[r * cols + c] : -1;
        if (clueL == 1 && clueR == 1) {
            if (!setEdgeState(eB, -1)) return false;
        }
        if (clueL == 1 && clueR == 3) {
            if (eR != -1 && !setEdgeState(eR, 1)) return false;
            int leftEdge = getVEdgeIndex(r, c - 1);
            int bottomEdge = getHEdgeIndex(r + 1, c - 1);
            if (leftEdge != -1 && !setEdgeState(leftEdge, -1)) return false;
            if (bottomEdge != -1 && !setEdgeState(bottomEdge, -1)) return false;
        }
        if (clueL == 3 && clueR == 1) {
            if (eL != -1 && !setEdgeState(eL, 1)) return false;
            int rightEdge = getVEdgeIndex(r, c + 1);
            int bottomEdge = getHEdgeIndex(r + 1, c);
            if (rightEdge != -1 && !setEdgeState(rightEdge, -1)) return false;
            if (bottomEdge != -1 && !setEdgeState(bottomEdge, -1)) return false;
        }
    }
    
    // If Bottom is CROSS, evaluate Top edge (separates Top-Left and Top-Right cells)
    if (stateB == -1 && eT != -1) {
        int clueL = (c > 0 && r > 0) ? clues[(r - 1) * cols + (c - 1)] : -1;
        int clueR = (c < cols && r > 0) ? clues[(r - 1) * cols + c] : -1;
        if (clueL == 1 && clueR == 1) {
            if (!setEdgeState(eT, -1)) return false;
        }
        if (clueL == 1 && clueR == 3) {
            if (eR != -1 && !setEdgeState(eR, 1)) return false;
            int leftEdge = getVEdgeIndex(r - 1, c - 1);
            int topEdge = getHEdgeIndex(r - 1, c - 1);
            if (leftEdge != -1 && !setEdgeState(leftEdge, -1)) return false;
            if (topEdge != -1 && !setEdgeState(topEdge, -1)) return false;
        }
        if (clueL == 3 && clueR == 1) {
            if (eL != -1 && !setEdgeState(eL, 1)) return false;
            int rightEdge = getVEdgeIndex(r - 1, c + 1);
            int topEdge = getHEdgeIndex(r - 1, c);
            if (rightEdge != -1 && !setEdgeState(rightEdge, -1)) return false;
            if (topEdge != -1 && !setEdgeState(topEdge, -1)) return false;
        }
    }
    
    // If Left is CROSS, evaluate Right edge (separates Top-Right and Bottom-Right cells)
    if (stateL == -1 && eR != -1) {
        int clueT = (r > 0 && c < cols) ? clues[(r - 1) * cols + c] : -1;
        int clueB = (r < rows && c < cols) ? clues[r * cols + c] : -1;
        if (clueT == 1 && clueB == 1) {
            if (!setEdgeState(eR, -1)) return false;
        }
        if (clueT == 1 && clueB == 3) {
            if (eB != -1 && !setEdgeState(eB, 1)) return false;
            int topEdge = getHEdgeIndex(r - 1, c);
            int rightEdge = getVEdgeIndex(r - 1, c + 1);
            if (topEdge != -1 && !setEdgeState(topEdge, -1)) return false;
            if (rightEdge != -1 && !setEdgeState(rightEdge, -1)) return false;
        }
        if (clueT == 3 && clueB == 1) {
            if (eT != -1 && !setEdgeState(eT, 1)) return false;
            int bottomEdge = getHEdgeIndex(r + 1, c);
            int rightEdge = getVEdgeIndex(r, c + 1);
            if (bottomEdge != -1 && !setEdgeState(bottomEdge, -1)) return false;
            if (rightEdge != -1 && !setEdgeState(rightEdge, -1)) return false;
        }
    }
    
    // If Right is CROSS, evaluate Left edge (separates Top-Left and Bottom-Left cells)
    if (stateR == -1 && eL != -1) {
        int clueT = (r > 0 && c > 0) ? clues[(r - 1) * cols + (c - 1)] : -1;
        int clueB = (r < rows && c > 0) ? clues[r * cols + (c - 1)] : -1;
        if (clueT == 1 && clueB == 1) {
            if (!setEdgeState(eL, -1)) return false;
        }
        if (clueT == 1 && clueB == 3) {
            if (eB != -1 && !setEdgeState(eB, 1)) return false;
            int topEdge = getHEdgeIndex(r - 1, c - 1);
            int leftEdge = getVEdgeIndex(r - 1, c - 1);
            if (topEdge != -1 && !setEdgeState(topEdge, -1)) return false;
            if (leftEdge != -1 && !setEdgeState(leftEdge, -1)) return false;
        }
        if (clueT == 3 && clueB == 1) {
            if (eT != -1 && !setEdgeState(eT, 1)) return false;
            int bottomEdge = getHEdgeIndex(r + 1, c - 1);
            int leftEdge = getVEdgeIndex(r, c - 1);
            if (bottomEdge != -1 && !setEdgeState(bottomEdge, -1)) return false;
            if (leftEdge != -1 && !setEdgeState(leftEdge, -1)) return false;
        }
    }

    return true;
}

// --- UNIVERSAL PARITY CHECK (TARJAN'S ALGORITHM) ---
static int bridgeTimer = 0;
static int bridgeDisc[MAX_DOTS];
static int bridgeLow[MAX_DOTS];
static bool bridgeVisited[MAX_DOTS];

static inline int min_int(int a, int b) { return a < b ? a : b; }

static bool universalParityDFS(int u, int p, int* out_sum_deg) {
    bridgeVisited[u] = true;
    bridgeTimer++;
    bridgeDisc[u] = bridgeLow[u] = bridgeTimer;

    int edges[4];
    int r = u / (cols + 1);
    int c = u % (cols + 1);
    int count = getDotEdges(r, c, edges);

    int my_sum_deg = 0;

    for (int i = 0; i < count; i++) {
        int e = edges[i];
        
        // Count already drawn lines incident to this dot
        if (edgeStates[e] == 1) {
            my_sum_deg++;
        }
        
        // Only traverse undecided edges to find bridges in the undecided graph
        if (edgeStates[e] != 0) continue; 

        int v;
        if (e < numH) {
            int er = e / cols;
            int ec = e % cols;
            int dotA = er * (cols + 1) + ec;
            v = (dotA == u) ? (dotA + 1) : dotA;
        } else {
            int vIdx = e - numH;
            int er = vIdx / (cols + 1);
            int ec = vIdx % (cols + 1);
            int dotA = er * (cols + 1) + ec;
            v = (dotA == u) ? (dotA + cols + 1) : dotA;
        }

        if (v == p) continue;

        if (bridgeVisited[v]) {
            bridgeLow[u] = min_int(bridgeLow[u], bridgeDisc[v]);
        } else {
            int child_sum_deg = 0;
            if (!universalParityDFS(v, u, &child_sum_deg)) return false;
            
            my_sum_deg += child_sum_deg;
            bridgeLow[u] = min_int(bridgeLow[u], bridgeLow[v]);

            if (bridgeLow[v] > bridgeDisc[u]) {
                // 'e' is a bridge in the undecided graph!
                if (child_sum_deg % 2 == 0) {
                    // Even number of lines cross the cut. 'e' must be a cross.
                    if (!setEdgeState(e, -1)) return false;
                } else {
                    // Odd number of lines cross the cut. 'e' must be a line.
                    if (!setEdgeState(e, 1)) return false;
                }
            }
        }
    }
    
    *out_sum_deg = my_sum_deg;
    return true;
}

static inline bool runUniversalParityCheck() {
    bridgeTimer = 0;
    memset(bridgeVisited, 0, numDots * sizeof(bool));
    
    for (int i = 0; i < numDots; i++) {
        if (!bridgeVisited[i]) {
            int root_sum_deg = 0;
            if (!universalParityDFS(i, -1, &root_sum_deg)) return false;
        }
    }
    return true;
}
// ---------------------------------------------

// Removed old O(V^3) runGF2Solver

static inline bool deductIncremental() {
    int loopCount = 0;
    while (true) {
        loopCount++;
        if (loopCount > 10000) {
            printf("[C ERROR] deductIncremental infinite loop detected! stack sizes: cells=%d, dots=%d\n", 
                   cellStackTop, dotStackTop);
            return false; // Force stop
        }
        while (cellStackTop > 0 || dotStackTop > 0 || gf2_queue_head < gf2_queue_tail) {
            // 1. Process cells
            int cellIdx = popCell();
            if (cellIdx != -1) {
                dbgSource = "cell";
                dbgCell = cellIdx;
                dbgDot = -1;
                int r = cellIdx / cols;
                int c = cellIdx % cols;
                int clue = clues[cellIdx];
                if (clue != -1) {
                    if (!check23CornerLogic(r, c)) return false;
                    if (!check22CornerLogic(r, c)) return false;
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
                        
                        int status;
                        // Down-Right dot is eB, eR. Opposite is eT, eL.
                        status = checkDiagonalChain(clue, r, c, 1, 1);
                        if (status & 1) { if (!setEdgeState(eT, 1)) return false; if (!setEdgeState(eL, 1)) return false; }
                        if (status & 2) { if (!setEdgeState(eB, 1)) return false; if (!setEdgeState(eR, 1)) return false; }
                        // Down-Left dot is eB, eL. Opposite is eT, eR.
                        status = checkDiagonalChain(clue, r, c, 1, -1);
                        if (status & 1) { if (!setEdgeState(eT, 1)) return false; if (!setEdgeState(eR, 1)) return false; }
                        if (status & 2) { if (!setEdgeState(eB, 1)) return false; if (!setEdgeState(eL, 1)) return false; }
                        // Up-Right dot is eT, eR. Opposite is eB, eL.
                        status = checkDiagonalChain(clue, r, c, -1, 1);
                        if (status & 1) { if (!setEdgeState(eB, 1)) return false; if (!setEdgeState(eL, 1)) return false; }
                        if (status & 2) { if (!setEdgeState(eT, 1)) return false; if (!setEdgeState(eR, 1)) return false; }
                        // Up-Left dot is eT, eL. Opposite is eB, eR.
                        status = checkDiagonalChain(clue, r, c, -1, -1);
                        if (status & 1) { if (!setEdgeState(eB, 1)) return false; if (!setEdgeState(eR, 1)) return false; }
                        if (status & 2) { if (!setEdgeState(eT, 1)) return false; if (!setEdgeState(eL, 1)) return false; }

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
                        
                        int status;
                        // Down-Right dot is eB, eR. Opposite is eT, eL.
                        status = checkDiagonalChain(clue, r, c, 1, 1);
                        if (status & 1) { if (!setEdgeState(eT, -1)) return false; if (!setEdgeState(eL, -1)) return false; }
                        if (status & 2) { if (!setEdgeState(eB, -1)) return false; if (!setEdgeState(eR, -1)) return false; }
                        // Down-Left dot is eB, eL. Opposite is eT, eR.
                        status = checkDiagonalChain(clue, r, c, 1, -1);
                        if (status & 1) { if (!setEdgeState(eT, -1)) return false; if (!setEdgeState(eR, -1)) return false; }
                        if (status & 2) { if (!setEdgeState(eB, -1)) return false; if (!setEdgeState(eL, -1)) return false; }
                        // Up-Right dot is eT, eR. Opposite is eB, eL.
                        status = checkDiagonalChain(clue, r, c, -1, 1);
                        if (status & 1) { if (!setEdgeState(eB, -1)) return false; if (!setEdgeState(eL, -1)) return false; }
                        if (status & 2) { if (!setEdgeState(eT, -1)) return false; if (!setEdgeState(eR, -1)) return false; }
                        // Up-Left dot is eT, eL. Opposite is eB, eR.
                        status = checkDiagonalChain(clue, r, c, -1, -1);
                        if (status & 1) { if (!setEdgeState(eB, -1)) return false; if (!setEdgeState(eR, -1)) return false; }
                        if (status & 2) { if (!setEdgeState(eT, -1)) return false; if (!setEdgeState(eL, -1)) return false; }

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
                        
                        // int status;
                        // // Down-Right dot is eB, eR. Opposite is eT, eL.
                        // status = checkDiagonalChain(r, c, 1, 1);
                        // if (status & 1) {
                        //     if (edgeStates[eT] == -1 && edgeStates[eL] == 0) { if (!setEdgeState(eL, 1)) return false; }
                        //     if (edgeStates[eL] == -1 && edgeStates[eT] == 0) { if (!setEdgeState(eT, 1)) return false; }
                        // }
                        // if (status & 2) {
                        //     if (edgeStates[eB] == 1 && edgeStates[eR] == 0) { if (!setEdgeState(eR, 1)) return false; }
                        //     if (edgeStates[eR] == 1 && edgeStates[eB] == 0) { if (!setEdgeState(eB, 1)) return false; }
                        //     if (edgeStates[eB] == -1 && edgeStates[eR] == 0) { if (!setEdgeState(eR, -1)) return false; }
                        //     if (edgeStates[eR] == -1 && edgeStates[eB] == 0) { if (!setEdgeState(eB, -1)) return false; }
                        // }
                        // // Down-Left dot is eB, eL. Opposite is eT, eR.
                        // status = checkDiagonalChain(r, c, 1, -1);
                        // if (status & 1) {
                        //     if (edgeStates[eT] == -1 && edgeStates[eR] == 0) { if (!setEdgeState(eR, 1)) return false; }
                        //     if (edgeStates[eR] == -1 && edgeStates[eT] == 0) { if (!setEdgeState(eT, 1)) return false; }
                        // }
                        // if (status & 2) {
                        //     if (edgeStates[eB] == 1 && edgeStates[eL] == 0) { if (!setEdgeState(eL, 1)) return false; }
                        //     if (edgeStates[eL] == 1 && edgeStates[eB] == 0) { if (!setEdgeState(eB, 1)) return false; }
                        //     if (edgeStates[eB] == -1 && edgeStates[eL] == 0) { if (!setEdgeState(eL, -1)) return false; }
                        //     if (edgeStates[eL] == -1 && edgeStates[eB] == 0) { if (!setEdgeState(eB, -1)) return false; }
                        // }
                        // // Up-Right dot is eT, eR. Opposite is eB, eL.
                        // status = checkDiagonalChain(r, c, -1, 1);
                        // if (status & 1) {
                        //     if (edgeStates[eB] == -1 && edgeStates[eL] == 0) { if (!setEdgeState(eL, 1)) return false; }
                        //     if (edgeStates[eL] == -1 && edgeStates[eB] == 0) { if (!setEdgeState(eB, 1)) return false; }
                        // }
                        // if (status & 2) {
                        //     if (edgeStates[eT] == 1 && edgeStates[eR] == 0) { if (!setEdgeState(eR, 1)) return false; }
                        //     if (edgeStates[eR] == 1 && edgeStates[eT] == 0) { if (!setEdgeState(eT, 1)) return false; }
                        //     if (edgeStates[eT] == -1 && edgeStates[eR] == 0) { if (!setEdgeState(eR, -1)) return false; }
                        //     if (edgeStates[eR] == -1 && edgeStates[eT] == 0) { if (!setEdgeState(eT, -1)) return false; }
                        // }
                        // // Up-Left dot is eT, eL. Opposite is eB, eR.
                        // status = checkDiagonalChain(r, c, -1, -1);
                        // if (status & 1) {
                        //     if (edgeStates[eB] == -1 && edgeStates[eR] == 0) { if (!setEdgeState(eR, 1)) return false; }
                        //     if (edgeStates[eR] == -1 && edgeStates[eB] == 0) { if (!setEdgeState(eB, 1)) return false; }
                        // }
                        // if (status & 2) {
                        //     if (edgeStates[eT] == 1 && edgeStates[eL] == 0) { if (!setEdgeState(eL, 1)) return false; }
                        //     if (edgeStates[eL] == 1 && edgeStates[eT] == 0) { if (!setEdgeState(eT, 1)) return false; }
                        //     if (edgeStates[eT] == -1 && edgeStates[eL] == 0) { if (!setEdgeState(eL, -1)) return false; }
                        //     if (edgeStates[eL] == -1 && edgeStates[eT] == 0) { if (!setEdgeState(eT, -1)) return false; }
                        // }
                    }
                    
                    // Universal SLE Propagation
                    // If any corner has exactly 1 line and 1 cross, it shoots an SLE diagonally.
                    int eT = cellEdges[0];
                    int eR = cellEdges[1];
                    int eB = cellEdges[2];
                    int eL = cellEdges[3];
                    if (edgeStates[eT] != 0 && edgeStates[eL] != 0 && edgeStates[eT] != edgeStates[eL]) {
                        if (!propagateDiagonal2s(r - 1, c - 1, -1, -1)) return false;
                        if (clue == 2 && (edgeStates[eB] == 0 || edgeStates[eR] == 0)) {
                            if (!propagateDiagonal2s(r + 1, c + 1, 1, 1)) return false;
                        }
                    }
                    if (edgeStates[eT] != 0 && edgeStates[eR] != 0 && edgeStates[eT] != edgeStates[eR]) {
                        if (!propagateDiagonal2s(r - 1, c + 1, -1, 1)) return false;
                        if (clue == 2 && (edgeStates[eB] == 0 || edgeStates[eL] == 0)) {
                            if (!propagateDiagonal2s(r + 1, c - 1, 1, -1)) return false;
                        }
                    }
                    if (edgeStates[eB] != 0 && edgeStates[eL] != 0 && edgeStates[eB] != edgeStates[eL]) {
                        if (!propagateDiagonal2s(r + 1, c - 1, 1, -1)) return false;
                        if (clue == 2 && (edgeStates[eT] == 0 || edgeStates[eR] == 0)) {
                            if (!propagateDiagonal2s(r - 1, c + 1, -1, 1)) return false;
                        }
                    }
                    if (edgeStates[eB] != 0 && edgeStates[eR] != 0 && edgeStates[eB] != edgeStates[eR]) {
                        if (!propagateDiagonal2s(r + 1, c + 1, 1, 1)) return false;
                        if (clue == 2 && (edgeStates[eT] == 0 || edgeStates[eL] == 0)) {
                            if (!propagateDiagonal2s(r - 1, c - 1, -1, -1)) return false;
                        }
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
            int dotIdx = popDot();
            if (dotIdx != -1) {
                dbgSource = "dot";
                dbgDot = dotIdx;
                dbgCell = -1;
                int r = dotIdx / (cols + 1);
                int c = dotIdx % (cols + 1);
                
                // --- NEW GENERALIZED 1-1 / 1-3 DOT BORDER LOGIC ---
                if (enableAdvancedAC3) {
                    if (!checkDotBorderLogic(r, c)) return false;
                }
                // --------------------------------------------------

                int dotEdges[4];
                int dotEdgesCount = getDotEdges(r, c, dotEdges);
                int lines = 0;
                int crosses = 0;
                int undecided[4];
                int undecidedCount = 0;
                
                for (int i = 0; i < dotEdgesCount; i++) {
                    int edgeIdx = dotEdges[i];
                    if (edgeStates[edgeIdx] == 1) lines++;
                    else if (edgeStates[edgeIdx] == -1) crosses++;
                    else {
                        // --- PREMATURE LOOP PREVENTION ---
                        if (enableAdvancedAC3) {
                            int dotA, dotB;
                            if (edgeIdx < numH) {
                                int er = edgeIdx / cols;
                                int ec = edgeIdx % cols;
                                dotA = er * (cols + 1) + ec;
                                dotB = dotA + 1;
                            } else {
                                int vIdx = edgeIdx - numH;
                                int er = vIdx / (cols + 1);
                                int ec = vIdx % (cols + 1);
                                dotA = er * (cols + 1) + ec;
                                dotB = dotA + (cols + 1);
                            }
                            if (dsuFind(dotA) == dsuFind(dotB)) {
                                // Connecting these dots forms a loop. Check if it's the valid final loop.
                                edgeStates[edgeIdx] = 1;
                                bool solved = isSolved();
                                edgeStates[edgeIdx] = 0;
                                if (!solved) {
                                    // It is a premature small loop. It must be a cross!
                                    if (!setEdgeState(edgeIdx, -1)) return false;
                                    crosses++;
                                    continue;
                                }
                            }
                        }
                        // ---------------------------------
                        
                        undecided[undecidedCount++] = edgeIdx;
                    }
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
                
                // 4. Generalized Rule: Line entering a 2 corner with opposite known
                // Bottom-Right cell (cr=r, cc=c)
                if (getClue(r, c) == 2) {
                    bool entered = (edgeStates[eL] == 1 && edgeStates[eT] == -1) || (edgeStates[eL] == -1 && edgeStates[eT] == 1);
                    bool entering_possible = (edgeStates[eL] == 1 && edgeStates[eT] == 0) || (edgeStates[eL] == 0 && edgeStates[eT] == 1);
                    int oppB = getHEdgeIndex(r + 1, c);
                    int oppR = getVEdgeIndex(r, c + 1);
                    if (entering_possible && (edgeStates[oppB] == -1 || edgeStates[oppR] == -1)) {
                        if (edgeStates[eL] != 1) { if (!setEdgeState(eL, -1)) return false; }
                        if (edgeStates[eT] != 1) { if (!setEdgeState(eT, -1)) return false; }
                        entered = true;
                    }
                    if (entered) {
                        if (edgeStates[oppB] == -1) { if (!setEdgeState(oppR, 1)) return false; }
                        else if (edgeStates[oppB] == 1) { if (!setEdgeState(oppR, -1)) return false; }
                        if (edgeStates[oppR] == -1) { if (!setEdgeState(oppB, 1)) return false; }
                        else if (edgeStates[oppR] == 1) { if (!setEdgeState(oppB, -1)) return false; }
                    }
                }
                // Bottom-Left cell (cr=r, cc=c-1)
                if (getClue(r, c - 1) == 2) {
                    bool entered = (edgeStates[eR] == 1 && edgeStates[eT] == -1) || (edgeStates[eR] == -1 && edgeStates[eT] == 1);
                    bool entering_possible = (edgeStates[eR] == 1 && edgeStates[eT] == 0) || (edgeStates[eR] == 0 && edgeStates[eT] == 1);
                    int oppB = getHEdgeIndex(r + 1, c - 1);
                    int oppL = getVEdgeIndex(r, c - 1);
                    if (entering_possible && (edgeStates[oppB] == -1 || edgeStates[oppL] == -1)) {
                        if (edgeStates[eR] != 1) { if (!setEdgeState(eR, -1)) return false; }
                        if (edgeStates[eT] != 1) { if (!setEdgeState(eT, -1)) return false; }
                        entered = true;
                    }
                    if (entered) {
                        if (edgeStates[oppB] == -1) { if (!setEdgeState(oppL, 1)) return false; }
                        else if (edgeStates[oppB] == 1) { if (!setEdgeState(oppL, -1)) return false; }
                        if (edgeStates[oppL] == -1) { if (!setEdgeState(oppB, 1)) return false; }
                        else if (edgeStates[oppL] == 1) { if (!setEdgeState(oppB, -1)) return false; }
                    }
                }
                // Top-Right cell (cr=r-1, cc=c)
                if (getClue(r - 1, c) == 2) {
                    bool entered = (edgeStates[eL] == 1 && edgeStates[eB] == -1) || (edgeStates[eL] == -1 && edgeStates[eB] == 1);
                    bool entering_possible = (edgeStates[eL] == 1 && edgeStates[eB] == 0) || (edgeStates[eL] == 0 && edgeStates[eB] == 1);
                    int oppT = getHEdgeIndex(r - 1, c);
                    int oppR = getVEdgeIndex(r - 1, c + 1);
                    if (entering_possible && (edgeStates[oppT] == -1 || edgeStates[oppR] == -1)) {
                        if (edgeStates[eL] != 1) { if (!setEdgeState(eL, -1)) return false; }
                        if (edgeStates[eB] != 1) { if (!setEdgeState(eB, -1)) return false; }
                        entered = true;
                    }
                    if (entered) {
                        if (edgeStates[oppT] == -1) { if (!setEdgeState(oppR, 1)) return false; }
                        else if (edgeStates[oppT] == 1) { if (!setEdgeState(oppR, -1)) return false; }
                        if (edgeStates[oppR] == -1) { if (!setEdgeState(oppT, 1)) return false; }
                        else if (edgeStates[oppR] == 1) { if (!setEdgeState(oppT, -1)) return false; }
                    }
                }
                // Top-Left cell (cr=r-1, cc=c-1)
                if (getClue(r - 1, c - 1) == 2) {
                    bool entered = (edgeStates[eR] == 1 && edgeStates[eB] == -1) || (edgeStates[eR] == -1 && edgeStates[eB] == 1);
                    bool entering_possible = (edgeStates[eR] == 1 && edgeStates[eB] == 0) || (edgeStates[eR] == 0 && edgeStates[eB] == 1);
                    int oppT = getHEdgeIndex(r - 1, c - 1);
                    int oppL = getVEdgeIndex(r - 1, c - 1);
                    if (entering_possible && (edgeStates[oppT] == -1 || edgeStates[oppL] == -1)) {
                        if (edgeStates[eR] != 1) { if (!setEdgeState(eR, -1)) return false; }
                        if (edgeStates[eB] != 1) { if (!setEdgeState(eB, -1)) return false; }
                        entered = true;
                    }
                    if (entered) {
                        if (edgeStates[oppT] == -1) { if (!setEdgeState(oppL, 1)) return false; }
                        else if (edgeStates[oppT] == 1) { if (!setEdgeState(oppL, -1)) return false; }
                        if (edgeStates[oppL] == -1) { if (!setEdgeState(oppT, 1)) return false; }
                        else if (edgeStates[oppL] == 1) { if (!setEdgeState(oppT, -1)) return false; }
                    }
                }

                // 5. Generalized Rule: Line entering a 1 corner
                // Bottom-Right cell (cr=r, cc=c)
                if (getClue(r, c) == 1) {
                    bool entered = (edgeStates[eL] == 1 && edgeStates[eT] == -1) || (edgeStates[eL] == -1 && edgeStates[eT] == 1);
                    if (entered) {
                        if (!setEdgeState(getHEdgeIndex(r + 1, c), -1)) return false;
                        if (!setEdgeState(getVEdgeIndex(r, c + 1), -1)) return false;
                    }
                }
                // Bottom-Left cell (cr=r, cc=c-1)
                if (getClue(r, c - 1) == 1) {
                    bool entered = (edgeStates[eR] == 1 && edgeStates[eT] == -1) || (edgeStates[eR] == -1 && edgeStates[eT] == 1);
                    if (entered) {
                        if (!setEdgeState(getHEdgeIndex(r + 1, c - 1), -1)) return false;
                        if (!setEdgeState(getVEdgeIndex(r, c - 1), -1)) return false;
                    }
                }
                // Top-Right cell (cr=r-1, cc=c)
                if (getClue(r - 1, c) == 1) {
                    bool entered = (edgeStates[eL] == 1 && edgeStates[eB] == -1) || (edgeStates[eL] == -1 && edgeStates[eB] == 1);
                    if (entered) {
                        if (!setEdgeState(getHEdgeIndex(r - 1, c), -1)) return false;
                        if (!setEdgeState(getVEdgeIndex(r - 1, c + 1), -1)) return false;
                    }
                }
                if (getClue(r - 1, c - 1) == 1) {
                    bool entered = (edgeStates[eR] == 1 && edgeStates[eB] == -1) || (edgeStates[eR] == -1 && edgeStates[eB] == 1);
                    if (entered) {
                        if (!setEdgeState(getHEdgeIndex(r - 1, c - 1), -1)) return false;
                        if (!setEdgeState(getVEdgeIndex(r - 1, c - 1), -1)) return false;
                    }
                }
            }
            
            // 3. Process GF(2)
            if (gf2_queue_head < gf2_queue_tail) {
                int e = gf2_update_queue[gf2_queue_head++];
                int val = (edgeStates[e] == 1) ? 1 : 0;
                if (!updateGlobalGF2(e, val)) return false;
            }
        }
        
        if (restrictLogicToLocal) {
            if (cellStackTop == 0 && dotStackTop == 0 && gf2_queue_head == gf2_queue_tail) {
                break;
            }
            continue;
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
        
        if (cellStackTop == 0 && dotStackTop == 0 && !cycleChanged) {
            // Only when absolutely everything is exhausted, run the O(V+E) Bridge Detection
            if (enableAdvancedAC3) {
                if (!runUniversalParityCheck()) return false;
            }
            
            if (cellStackTop == 0 && dotStackTop == 0 && gf2_queue_head == gf2_queue_tail) {
                break;
            }
        }
    }
    return true;
}

EMSCRIPTEN_KEEPALIVE
bool deduct() {
    dsuInitFromCurrent();
    clearStacks();
    
    // initial push is removed because applyStaticRules handles pushing changed elements automatically
    
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
    memcpy(backupStackGF2Matrix[depth], global_gf2_matrix, sizeof(global_gf2_matrix));
    memcpy(backupStackGF2Constants[depth], global_gf2_constants, sizeof(global_gf2_constants));
    memcpy(backupStackGF2Pivot[depth], global_gf2_pivot, sizeof(global_gf2_pivot));
    int dsuCheckpoint = dsuHistoryCount;

    // Run logical deduction rules: full pass at depth 0, incremental pass at depth > 0
    if (depth == 0) {
        if (!deduct()) {
            memcpy(edgeStates, backupStack[depth], numEdges);
            memcpy(global_gf2_matrix, backupStackGF2Matrix[depth], sizeof(global_gf2_matrix));
            memcpy(global_gf2_constants, backupStackGF2Constants[depth], sizeof(global_gf2_constants));
            memcpy(global_gf2_pivot, backupStackGF2Pivot[depth], sizeof(global_gf2_pivot));
            gf2_queue_head = 0; gf2_queue_tail = 0;
            clearStacks();
            dsuRollback(dsuCheckpoint);
            return;
        }
    } else {
        if (!deductIncremental()) {
            memcpy(edgeStates, backupStack[depth], numEdges);
            memcpy(global_gf2_matrix, backupStackGF2Matrix[depth], sizeof(global_gf2_matrix));
            memcpy(global_gf2_constants, backupStackGF2Constants[depth], sizeof(global_gf2_constants));
            memcpy(global_gf2_pivot, backupStackGF2Pivot[depth], sizeof(global_gf2_pivot));
            gf2_queue_head = 0; gf2_queue_tail = 0;
            clearStacks();
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
        memcpy(global_gf2_matrix, backupStackGF2Matrix[depth], sizeof(global_gf2_matrix));
        memcpy(global_gf2_constants, backupStackGF2Constants[depth], sizeof(global_gf2_constants));
        memcpy(global_gf2_pivot, backupStackGF2Pivot[depth], sizeof(global_gf2_pivot));
        gf2_queue_head = 0; gf2_queue_tail = 0;
        clearStacks();
        dsuRollback(dsuCheckpoint);
        return;
    }

    if (foundSolutionsCount >= 2 || (findSingle && foundSolutionsCount >= 1)) {
        memcpy(edgeStates, backupStack[depth], numEdges);
        memcpy(global_gf2_matrix, backupStackGF2Matrix[depth], sizeof(global_gf2_matrix));
        memcpy(global_gf2_constants, backupStackGF2Constants[depth], sizeof(global_gf2_constants));
        memcpy(global_gf2_pivot, backupStackGF2Pivot[depth], sizeof(global_gf2_pivot));
        gf2_queue_head = 0; gf2_queue_tail = 0;
        clearStacks();
        dsuRollback(dsuCheckpoint);
        return;
    }

    // Save state AFTER deduction
    memcpy(backupAfterDeductStack[depth], edgeStates, numEdges);
    memcpy(backupAfterDeductStackGF2Matrix[depth], global_gf2_matrix, sizeof(global_gf2_matrix));
    memcpy(backupAfterDeductStackGF2Constants[depth], global_gf2_constants, sizeof(global_gf2_constants));
    memcpy(backupAfterDeductStackGF2Pivot[depth], global_gf2_pivot, sizeof(global_gf2_pivot));
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
    memcpy(global_gf2_matrix, backupAfterDeductStackGF2Matrix[depth], sizeof(global_gf2_matrix));
    memcpy(global_gf2_constants, backupAfterDeductStackGF2Constants[depth], sizeof(global_gf2_constants));
    memcpy(global_gf2_pivot, backupAfterDeductStackGF2Pivot[depth], sizeof(global_gf2_pivot));
    gf2_queue_head = 0; gf2_queue_tail = 0;
    clearStacks();

    if (foundSolutionsCount >= 2 || (findSingle && foundSolutionsCount >= 1) || isTimeout) {
        dsuRollback(dsuCheckpoint);
        memcpy(edgeStates, backupStack[depth], numEdges);
        memcpy(global_gf2_matrix, backupStackGF2Matrix[depth], sizeof(global_gf2_matrix));
        memcpy(global_gf2_constants, backupStackGF2Constants[depth], sizeof(global_gf2_constants));
        memcpy(global_gf2_pivot, backupStackGF2Pivot[depth], sizeof(global_gf2_pivot));
        gf2_queue_head = 0; gf2_queue_tail = 0;
        clearStacks();
        return;
    }

    // Try setting edge to -1 (cross)
    if (setEdgeState(branchIdx, -1)) {
        backtrack(depth + 1, findSingle, maxSteps);
    }
    dsuRollback(dsuCheckpointAfterDeduct);
    memcpy(edgeStates, backupAfterDeductStack[depth], numEdges);
    memcpy(global_gf2_matrix, backupAfterDeductStackGF2Matrix[depth], sizeof(global_gf2_matrix));
    memcpy(global_gf2_constants, backupAfterDeductStackGF2Constants[depth], sizeof(global_gf2_constants));
    memcpy(global_gf2_pivot, backupAfterDeductStackGF2Pivot[depth], sizeof(global_gf2_pivot));
    gf2_queue_head = 0; gf2_queue_tail = 0;
    clearStacks();
    
    // Cleanup to restore parent state
    dsuRollback(dsuCheckpoint);
    memcpy(edgeStates, backupStack[depth], numEdges);
    memcpy(global_gf2_matrix, backupStackGF2Matrix[depth], sizeof(global_gf2_matrix));
    memcpy(global_gf2_constants, backupStackGF2Constants[depth], sizeof(global_gf2_constants));
    memcpy(global_gf2_pivot, backupStackGF2Pivot[depth], sizeof(global_gf2_pivot));
    gf2_queue_head = 0; gf2_queue_tail = 0;
    clearStacks();
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

static inline bool isEdgeConstrained(int e) {
    int r, c, dotA, dotB;
    if (e < numH) {
        r = e / cols;
        c = e % cols;
        if (r > 0 && clues[(r - 1) * cols + c] != -1) return true;
        if (r < rows && clues[r * cols + c] != -1) return true;
        dotA = r * (cols + 1) + c;
        dotB = dotA + 1;
    } else {
        int vIdx = e - numH;
        r = vIdx / (cols + 1);
        c = vIdx % (cols + 1);
        if (c > 0 && clues[r * cols + (c - 1)] != -1) return true;
        if (c < cols && clues[r * cols + c] != -1) return true;
        dotA = r * (cols + 1) + c;
        dotB = dotA + (cols + 1);
    }
    
    int edges[4];
    int count = getDotEdges(dotA / (cols + 1), dotA % (cols + 1), edges);
    for (int i = 0; i < count; i++) {
        if (edges[i] != e && edgeStates[edges[i]] != 0) return true;
    }
    
    count = getDotEdges(dotB / (cols + 1), dotB % (cols + 1), edges);
    for (int i = 0; i < count; i++) {
        if (edges[i] != e && edgeStates[edges[i]] != 0) return true;
    }
    
    return false;
}

int lookaheadEdgeTests = 0;
int staticRuleEdgesTotal = 0;
int lutEdgesTotal = 0;
int lookaheadForcedEdgesTotal = 0;

int check_human_solvability() {
    dsuInitFromCurrent();
    clearStacks();
    
    lookaheadConfirmedCount = 0;
    
    // 1. Seed AC-3 queue is removed. applyStaticRules handles pushing changed elements automatically.
    
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
        
        if (lookaheadMaxLimit == 0) {
            return -2; // Stalled: Lookahead is disabled for this difficulty
        }

        changed = false;

        // 2. Perform 1-Step Lookahead on Undecided Edges
        for (int i = 0; i < numEdges; i++) {
            if (edgeStates[i] == 0) {
                if (!isEdgeConstrained(i)) continue; // Prune unconstrained edges
                
                // Scenario A: Assume Line (1)
                int checkpoint = dsuHistoryCount;
                int8_t backupEdges[MAX_EDGES];
                memcpy(backupEdges, edgeStates, numEdges);
                memcpy(check_gf2_matrix_backup, global_gf2_matrix, sizeof(global_gf2_matrix));
                memcpy(check_gf2_constants_backup, global_gf2_constants, sizeof(global_gf2_constants));
                memcpy(check_gf2_pivot_backup, global_gf2_pivot, sizeof(global_gf2_pivot));
                
                lookaheadConfirmedCount = 0;
                isDoingLookahead = true;
                lookaheadEdgeTests++;
                bool lineSuccess = setEdgeState(i, 1) && deductIncremental();
                isDoingLookahead = false;
                
                dsuRollback(checkpoint);
                memcpy(edgeStates, backupEdges, numEdges);
                memcpy(global_gf2_matrix, check_gf2_matrix_backup, sizeof(global_gf2_matrix));
                memcpy(global_gf2_constants, check_gf2_constants_backup, sizeof(global_gf2_constants));
                memcpy(global_gf2_pivot, check_gf2_pivot_backup, sizeof(global_gf2_pivot));
                gf2_queue_head = 0; gf2_queue_tail = 0;
                clearStacks();
                
                if (!lineSuccess) {
                    // Line leads to contradiction -> Must be Cross (-1)
                    extern int lookaheadForcedEdgesTotal;
                    lookaheadForcedEdgesTotal++;
                    if (!setEdgeState(i, -1)) return 0;
                    changed = true;
                    break; // Restart main propagation loop
                }
                
                // Scenario B: Assume Cross (-1)
                checkpoint = dsuHistoryCount;
                memcpy(backupEdges, edgeStates, numEdges);
                memcpy(check_gf2_matrix_backup, global_gf2_matrix, sizeof(global_gf2_matrix));
                memcpy(check_gf2_constants_backup, global_gf2_constants, sizeof(global_gf2_constants));
                memcpy(check_gf2_pivot_backup, global_gf2_pivot, sizeof(global_gf2_pivot));
                
                lookaheadConfirmedCount = 0;
                isDoingLookahead = true;
                lookaheadEdgeTests++;
                bool crossSuccess = setEdgeState(i, -1) && deductIncremental();
                isDoingLookahead = false;
                
                dsuRollback(checkpoint);
                memcpy(edgeStates, backupEdges, numEdges);
                memcpy(global_gf2_matrix, check_gf2_matrix_backup, sizeof(global_gf2_matrix));
                memcpy(global_gf2_constants, check_gf2_constants_backup, sizeof(global_gf2_constants));
                memcpy(global_gf2_pivot, check_gf2_pivot_backup, sizeof(global_gf2_pivot));
                gf2_queue_head = 0; gf2_queue_tail = 0;
                clearStacks();
                
                if (!crossSuccess) {
                    // Cross leads to contradiction -> Must be Line (1)
                    extern int lookaheadForcedEdgesTotal;
                    lookaheadForcedEdgesTotal++;
                    if (!setEdgeState(i, 1)) return 0;
                    changed = true;
                    break; // Restart main propagation loop
                }
            } // closes if (edgeStates[i] == 0)
        } // closes for loop
    } // closes while (changed)
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

static int compareCandidates(const void* a, const void* b) {
    Candidate* ca = (Candidate*)a;
    Candidate* cb = (Candidate*)b;
    if (cb->score > ca->score) return 1;
    if (cb->score < ca->score) return -1;
    return 0;
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
                                int brR = r + dy;
                                int brC = c + dx;
                                if (brR < 0 || brR + 3 >= rows || brC < 0 || brC + 3 >= cols) continue;
                                
                                bool blockFull = true;
                                for (int i = 0; i < 4; i++) {
                                    for (int j = 0; j < 4; j++) {
                                        if (i == -dy && j == -dx) continue;
                                        if (genCells[brR + i][brC + j] != 1) {
                                            blockFull = false;
                                            break;
                                        }
                                    }
                                    if (!blockFull) break;
                                }
                                if (blockFull) {
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

            // Sort candidates desc using qsort (much faster than bubble sort)
            qsort(candidates, candCount, sizeof(Candidate), compareCandidates);

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
    
    // For Easy mode, disable all global rules to ensure it can be solved purely by local patterns
    extern bool restrictLogicToLocal;
    restrictLogicToLocal = (strcmp(difficulty, "Easy") == 0 || strcmp(difficulty, "easy") == 0);

    if (strcmp(difficulty, "Easy") == 0 || strcmp(difficulty, "easy") == 0) {
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
        if (strcmp(difficulty, "Master") == 0 || strcmp(difficulty, "master") == 0) {
            lookaheadMaxLimit = 3; // Enable lookahead for Master
        } else {
            lookaheadMaxLimit = 0; // Disabled for Easy, Medium, Hard
        }
        // Human solvability check
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
    lookaheadEdgeTests = 0;
    lookaheadForcedEdgesTotal = 0;
    staticRuleEdgesTotal = 0;
    lutEdgesTotal = 0;
    
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
    double keepRatio = 0.0;
    if (strcmp(difficulty, "Easy") == 0 || strcmp(difficulty, "easy") == 0) keepRatio = 0.65;
    else if (strcmp(difficulty, "Medium") == 0 || strcmp(difficulty, "medium") == 0) keepRatio = 0.58;
    else keepRatio = 0.0; // Hard and Master will minimize to the limit

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
        
        if (strcmp(difficulty, "Master") == 0 || strcmp(difficulty, "Hard") == 0) {
            pairs[pairCount].priority = 0; // Pure random, no bias by default
            if (valA == 0 || valB == 0) {
                // To reduce 0s by about half in Hard/Master without eliminating them completely,
                // we assign high removal priority (-1) to ~60% of the 0-pairs.
                if ((rand() % 100) < 60) {
                    pairs[pairCount].priority = -1;
                }
            }
        } else {
            if (valA == 3 || valB == 3) {
                pairs[pairCount].priority = 2; // Keep 3 (check last)
            } else if (valA == 0 || valB == 0) {
                pairs[pairCount].priority = 2; // Keep 0 (check last)
            } else {
                pairs[pairCount].priority = 0; // Hide 1 and 2 first
            }
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

    fastPathCount = 0;
    solvabilityChecks = 0;
    lookaheadEdgeTests = 0;
    staticRuleEdgesTotal = 0;
    lutEdgesTotal = 0;
    
    printf("[C Generator] Starting symmetric minimization. Total cells: %d, Initial clues: %d, Target: %d\n", 
           totalCells, currentClueCount, targetKeepCount);
    
    // Check initial board solvability before any clue removal
    initSolvable = checkSolvability(difficulty);
    printf("Initial Board Solvability check: %d\n", initSolvable);


    // Pass 2: General removal (Batched)
    int batchSize = 16;
    int i = 0;
    while (i < pairCount && currentClueCount > targetKeepCount) {
        int actualBatch = 0;
        int savedCluesA[24];
        int savedCluesB[24];
        int savedIndices[24];
        int batchRemovedClues = 0;

        int b = 0;
        for (; b < batchSize && i + b < pairCount && currentClueCount - batchRemovedClues > targetKeepCount; b++) {
            int idx = i + b;
            int cellA = pairs[idx].cellA;
            if (cellA == -1) continue; // Skip if removed in Pass 1
            int cellB = pairs[idx].cellB;
            
            int8_t valA = clues[cellA];
            int8_t valB = clues[cellB];
            
            if (valA == -1 && valB == -1) continue;

            if ((strcmp(difficulty, "Easy") == 0 || strcmp(difficulty, "easy") == 0) && (valA == 3 || valB == 3) && ((double)rand() / RAND_MAX) < 0.8) {
                continue;
            }

            savedCluesA[actualBatch] = valA;
            savedCluesB[actualBatch] = valB;
            savedIndices[actualBatch] = idx;
            actualBatch++;
            
            clues[cellA] = -1;
            clues[cellB] = -1;
            batchRemovedClues += (cellA == cellB) ? 1 : 2;
        }

        if (actualBatch == 0) {
            i += (b == 0) ? 1 : b;
            continue;
        }

        currentClueCount -= batchRemovedClues;

        if (checkSolvability(difficulty)) {
            // Batch removal successful
            i += b;
        } else {
            // Batch failed! Rollback
            for (int k = 0; k < actualBatch; k++) {
                int idx = savedIndices[k];
                int cellA = pairs[idx].cellA;
                int cellB = pairs[idx].cellB;
                clues[cellA] = savedCluesA[k];
                clues[cellB] = savedCluesB[k];
            }
            currentClueCount += batchRemovedClues;
            
            if (batchSize > 1) {
                batchSize /= 2; // Progressively halve the batch size
            } else {
                // If batchSize is already 1, we just tried removing 1 pair and it failed. Skip this pair.
                i++;
            }
        }

        if ((i) % 10 == 0 || batchSize > 1) {
            printf("[C Generator] Progress: Checked %d/%d pairs | Clues remaining: %d | FastPath: %d | Timeouts: %d | BatchSize: %d | LookaheadTests: %d\n",
                   i, pairCount, currentClueCount, fastPathCount, debugTimeoutCount, batchSize, lookaheadEdgeTests);
#ifdef __EMSCRIPTEN__
            EM_ASM({
                if (typeof self !== 'undefined' && typeof self.reportProgress === 'function') {
                    self.reportProgress($0, $1);
                }
            }, i, pairCount);
#endif
        }
    }

    printf("[C Generator] Finished symmetric minimization! Final clues remaining: %d/%d (%d%%) | FastPath: %d/%d checks | LookaheadTests: %d | ForcedEdges: %d | StaticEdges: %d | LUTEdges: %d\n", 
           currentClueCount, totalCells, (currentClueCount * 100) / totalCells, fastPathCount, solvabilityChecks, lookaheadEdgeTests, lookaheadForcedEdgesTotal, staticRuleEdgesTotal, lutEdgesTotal);

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

EMSCRIPTEN_KEEPALIVE
void set_advanced_ac3(bool enable) {
    enableAdvancedAC3 = enable;
}

EMSCRIPTEN_KEEPALIVE
int get_lookahead_count() {
    return solvabilityChecks;
}

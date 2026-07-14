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

#define MAX_ROWS 50
#define MAX_COLS 50
#define MAX_CELLS 2500
#define MAX_EDGES 5500
#define MAX_DOTS 2700

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
bool enableGF2 = true;
bool prioritizeGF2 = true;

// Performance Tracking
double perf_static = 0;
double perf_lut = 0;
double perf_ac3 = 0;
double perf_gf2 = 0;
double perf_lookahead = 0;

EMSCRIPTEN_KEEPALIVE double get_perf_static() { return perf_static; }
EMSCRIPTEN_KEEPALIVE double get_perf_lut() { return perf_lut; }
EMSCRIPTEN_KEEPALIVE double get_perf_ac3() { return perf_ac3; }
EMSCRIPTEN_KEEPALIVE double get_perf_gf2() { return perf_gf2; }
EMSCRIPTEN_KEEPALIVE double get_perf_lookahead() { return perf_lookahead; }
EMSCRIPTEN_KEEPALIVE void reset_perf() { perf_static = 0; perf_lut = 0; perf_ac3 = 0; perf_gf2 = 0; perf_lookahead = 0; }


EMSCRIPTEN_KEEPALIVE
void set_prioritize_gf2(bool enabled) {
    prioritizeGF2 = enabled;
}

EMSCRIPTEN_KEEPALIVE
void set_solver_difficulty(const char* difficulty) {
    extern int lookaheadMaxLimit;
    if (strcmp(difficulty, "Easy") == 0 || strcmp(difficulty, "easy") == 0) {
        restrictLogicToLocal = true;
        enableGF2 = false;
        lookaheadMaxLimit = 0;
    } else if (strcmp(difficulty, "Medium") == 0 || strcmp(difficulty, "medium") == 0) {
        restrictLogicToLocal = false;
        enableGF2 = false;
        lookaheadMaxLimit = 0;
    } else if (strcmp(difficulty, "Hard") == 0 || strcmp(difficulty, "hard") == 0) {
        restrictLogicToLocal = false;
        enableGF2 = true;
        lookaheadMaxLimit = 0; // Disabled for generation by user request
    } else if (strcmp(difficulty, "Master") == 0 || strcmp(difficulty, "master") == 0) {
        restrictLogicToLocal = false;
        enableGF2 = true;
        lookaheadMaxLimit = 0; // Disabled for generation by user request
    }
}


// pre-allocated stack for backtracking search to avoid constant allocations
#define MAX_BACKTRACK_DEPTH 200
static int8_t backupStack[MAX_BACKTRACK_DEPTH][MAX_EDGES];
static int8_t backupAfterDeductStack[MAX_BACKTRACK_DEPTH][MAX_EDGES];

extern int ac3_current_rule_id;
extern int ac3_rule_hit_counts[256];
#define RECORD_AC3_HIT() do { \
    if (ac3_current_rule_id >= 0 && ac3_current_rule_id < 256) ac3_rule_hit_counts[ac3_current_rule_id]++; \
} while(0)

// Graph adjacency list arrays for loop connection tracing (avoids allocations)
static int adj[MAX_DOTS][4];
static int adjCount[MAX_DOTS];
static bool visitedDots[MAX_DOTS];

// GF(2) Area Parity Solver memory
#define MAX_GF2_EQS 5500
#define MAX_GF2_VARS 5500
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

static int colorDsuParent[MAX_CELLS * 2 + 2];
static int colorDsuRank[MAX_CELLS * 2 + 2];

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
bool applyLUT();
void init_boundary_luts();
bool applyBoundaryLUTs();

// Precompute LUTs automatically when the WASM module is loaded
__attribute__((constructor))
void precompute_luts_on_startup() {
    init_lut();
    init_boundary_luts();
}

// API functions
EMSCRIPTEN_KEEPALIVE
void init_grid(int r, int c) {
    init_lut();
    init_boundary_luts();
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

int deduction_history[MAX_EDGES * 2];
const char* deduction_rule_names[MAX_EDGES * 2];
int deduction_history_count = 0;
// Difficulty Levels
#define DIFF_BASIC     1
#define DIFF_EASY      2
#define DIFF_MEDIUM    3
#define DIFF_HARD      4
#define DIFF_GLOBAL_1  5
#define DIFF_GLOBAL_2  6
#define DIFF_GLOBAL_3  7
#define DIFF_EXTREME   8
#define DIFF_GLOBAL_4  9
#define DIFF_LOOKAHEAD 10

// AC3 Sub-profiling
double ac3_rule_times[256];
int ac3_rule_hit_counts[256];
int ac3_current_rule_id = -1;
double ac3_t_start = 0;
int ac3_current_difficulty_limit = DIFF_LOOKAHEAD;

EMSCRIPTEN_KEEPALIVE const char* get_ac3_rule_name(int idx) {
    switch (idx) {
        case 101: return "Basic (Cell Clue)";
        case 102: return "Basic (Dot Line Limit)";
        case 103: return "Basic (Dot Constraint)";
        case 104: return "Basic (0 All Crosses)";
        case 111: return "Easy (Corner 0)";
        case 112: return "Easy (Corner 3)";
        case 113: return "Easy (Adjacent 3s)";
        case 115: return "Medium (Clue 2 Diagonal Entry)";
        case 121: return "Medium (Corner 2)";
        case 122: return "Medium (Diagonal 1)";
        case 123: return "Medium (Diagonal 3)";
        case 124: return "Medium (Universal SLE)";
        case 125: return "Medium (General 2 XOR)";
        case 126: return "Medium (Corner Dot Heuristic)";
        case 131: return "Hard (Corner 3 Ext)";
        case 132: return "Hard (Corner 2 Pair)";
        case 133: return "Hard (Advanced 2)";
        case 134: return "Hard (Line entering 3)";
        case 135: return "Hard (Line entering 1)";
        case 136: return "Hard (Clue 2 Early SLE)";
        case 137: return "Hard (2 and 3 Diagonal)";
        case 138: return "Hard (Dot Border Theorem)";
        case 140: return "Hard (Diag 2-3 Outer X/Line)";
        case 141: return "Global (Early Closed Loop)";
        case 142: return "Global (Jordan Curve)";
        case 144: return "Global (Inside/Outside Coloring)";
        case 143: return "Global (Virtual Path Loop Prevention)";
        case 151: return "Global (GF2 Parity)";
        case 152: return "Global (Bridge Connectivity)";
        case 161: return "Extreme (LUT Deduction)";
        case 200: return "Lookahead (Depth)";
        case 201: return "Lookahead (Forcing)";
        default: return "";
    }
}
EMSCRIPTEN_KEEPALIVE double get_ac3_rule_time(int idx) {
    if (idx < 0 || idx >= 256) return 0;
    return ac3_rule_times[idx];
}
EMSCRIPTEN_KEEPALIVE int get_ac3_rule_hit_count(int idx) {
    if (idx < 0 || idx >= 256) return 0;
    return ac3_rule_hit_counts[idx];
}
EMSCRIPTEN_KEEPALIVE int get_ac3_rule_count() { return 256; }
EMSCRIPTEN_KEEPALIVE void reset_ac3_rule_times() {
    for (int i = 0; i < 256; i++) {
        ac3_rule_times[i] = 0;
        ac3_rule_hit_counts[i] = 0;
    }
}

#ifndef ENABLE_PROFILING
#define ENABLE_PROFILING 0
#endif
#if ENABLE_PROFILING
#define RECORD_AC3_TIME(new_id) do { \
    double _t = emscripten_get_now(); \
    if (ac3_current_rule_id >= 0 && ac3_current_rule_id < 256) ac3_rule_times[ac3_current_rule_id] += (_t - ac3_t_start); \
    ac3_t_start = _t; \
    ac3_current_rule_id = (new_id); \
    const char* _n = get_ac3_rule_name(new_id); \
    if (_n[0] != '\0') current_rule_name = _n; \
} while(0)
#else
#define RECORD_AC3_TIME(new_id) do { \
    ac3_current_rule_id = (new_id); \
    const char* _n = get_ac3_rule_name(new_id); \
    if (_n[0] != '\0') current_rule_name = _n; \
} while(0)
#endif

#define AC3_RETURN_FALSE do { RECORD_AC3_TIME(-1); return false; } while(0)
#define AC3_RETURN_TRUE do { RECORD_AC3_TIME(-1); return true; } while(0)

const char* current_rule_name = "不明なルール";

EMSCRIPTEN_KEEPALIVE const char* get_last_applied_rule_name() {
    return current_rule_name;
}

// --- Deduction Logging for Analysis ---
typedef struct {
    int edgeIdx;
    int ruleId;
    int depth; // lookahead depth (0 for base logic)
} DeductionLog;

DeductionLog deduction_logs[MAX_EDGES * 2];
int deduction_log_count = 0;
bool enable_deduction_logging = false;
int current_lookahead_depth = 0;

EMSCRIPTEN_KEEPALIVE
int get_first_deduced_edge() {
    if (deduction_history_count > 0) {
        return deduction_history[0];
    }
    return -1;
}

EMSCRIPTEN_KEEPALIVE
const char* get_first_deduced_rule_name() {
    if (deduction_history_count > 0) {
        return deduction_rule_names[0];
    }
    return "不明";
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

static inline bool setEdgeState_real(int edgeIdx, int8_t state, int line_no) {
    if (edgeIdx == numEdges) return state == -1; // Sentinel edge must be cross
    if (edgeIdx < 0 || edgeIdx > numEdges) {
        printf("[C ERROR] Invalid edge index %d (max %d) at line %d\n", edgeIdx, numEdges, line_no);
        return false;
    }
    if (edgeStates[edgeIdx] == state) return true; // Already set to this state
    if (edgeStates[edgeIdx] != 0) {
                return false;    // Contradiction
    }
    
    if (isDoingLookahead && lookaheadMaxLimit > 0 && lookaheadConfirmedCount >= lookaheadMaxLimit) {
        return true; // Limit reached: treat as success but do NOT change state to avoid wasteful AC-3 propagation
    }
    
    edgeStates[edgeIdx] = state;
    RECORD_AC3_HIT();
    
    if (enable_deduction_logging && !isDoingLookahead && deduction_log_count < MAX_EDGES * 2) {
        deduction_logs[deduction_log_count].edgeIdx = edgeIdx;
        deduction_logs[deduction_log_count].ruleId = ac3_current_rule_id;
        deduction_logs[deduction_log_count].depth = 0;
        deduction_log_count++;
    }
    
    if (deduction_history_count < MAX_EDGES * 2) {
        deduction_rule_names[deduction_history_count] = current_rule_name;
        deduction_history[deduction_history_count++] = edgeIdx;
    }

    gf2_update_queue[gf2_queue_tail++] = edgeIdx;
    
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

#define setEdgeState(idx, st) setEdgeState_real(idx, st, __LINE__)

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

static bool batchUpdateGlobalGF2() {
    if (gf2_queue_head == gf2_queue_tail) return true;
    
    bool row_modified[MAX_GF2_EQS] = {false};
    
    // 1. 全てのエッジを一括して行列から消去する
    while (gf2_queue_head < gf2_queue_tail) {
        int e = gf2_update_queue[gf2_queue_head++];
        int val = (edgeStates[e] == 1) ? 1 : 0;
        
        for (int r = 0; r < global_gf2_num_eqs; r++) {
            if (global_gf2_matrix[r][e / 64] & (1ULL << (e % 64))) {
                global_gf2_matrix[r][e / 64] &= ~(1ULL << (e % 64));
                global_gf2_constants[r] ^= val;
                row_modified[r] = true;
                
                if (global_gf2_pivot[r] == e) {
                    global_gf2_pivot[r] = -1; // ピボットを喪失
                }
            }
        }
    }
    
    // 2. ピボットを失った行の再ピボット選択と掃き出し
    for (int r = 0; r < global_gf2_num_eqs; r++) {
        if (global_gf2_pivot[r] == -1 && row_modified[r]) {
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
                        row_modified[i] = true; // 他の行も更新された
                    }
                }
            } else {
                if (global_gf2_constants[r] != 0) {
                    return false; // 矛盾発生
                }
            }
        }
    }
    
    // 3. 値が確定できる変数を探す
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

EMSCRIPTEN_KEEPALIVE
bool applyStaticRules_internal() {
    dsuInitFromCurrent();
    clearStacks();
    
    if (enableGF2) {
        initGlobalGF2();
        
        // Sync pre-existing edges into the GF2 update queue.
        for (int i = 0; i < numEdges; i++) {
            if (edgeStates[i] != 0) {
                gf2_update_queue[gf2_queue_tail++] = i;
            }
        }
    }

    dbgSource = "static_rules";

    for (int r = 0; r < rows; r++) {
        for (int c = 0; c < cols; c++) {
            int clue = clues[r * cols + c];
            if (clue == -1) continue;
            
            // Rule 1: Clue 0 (All edges are crosses)
            if (clue == 0) {
                RECORD_AC3_TIME(104);
                if (!setEdgeState(getHEdgeIndex(r, c), -1)) return false;
                if (!setEdgeState(getVEdgeIndex(r, c), -1)) return false;
                if (!setEdgeState(getHEdgeIndex(r + 1, c), -1)) return false;
                if (!setEdgeState(getVEdgeIndex(r, c + 1), -1)) return false;
                continue;
            }
            
            // Rule 2.1: Orthogonally Adjacent 3-3 Cells
            if (clue == 3) {
                RECORD_AC3_TIME(113);
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
                RECORD_AC3_TIME(131);
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

    extern bool restrictLogicToLocal;
    if (!restrictLogicToLocal) {
        double t_lut_start = emscripten_get_now();
        if (!enable_deduction_logging) {
            RECORD_AC3_TIME(161);
            if (!applyLUT()) return false;
            
            RECORD_AC3_TIME(161);
            if (!applyBoundaryLUTs()) return false;
        }
        perf_lut += emscripten_get_now() - t_lut_start;
        
        int afterLUT = 0;
        for(int i=0; i<numEdges; i++) if(edgeStates[i] != 0) afterLUT++;
        extern int lutEdgesTotal;
        lutEdgesTotal += (afterLUT - afterStatic);
    }

    return true;
}

EMSCRIPTEN_KEEPALIVE
bool applyStaticRules() {
    double t0 = emscripten_get_now();
    bool res = applyStaticRules_internal();
    perf_static += emscripten_get_now() - t0;
    return res;
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

static inline void colorDsuInit(int n) {
    for (int i = 0; i < n; i++) {
        colorDsuParent[i] = i;
        colorDsuRank[i] = 0;
    }
}

static inline int colorDsuFind(int i) {
    int root = i;
    while (root != colorDsuParent[root]) {
        root = colorDsuParent[root];
    }
    int curr = i;
    while (curr != root) {
        int nxt = colorDsuParent[curr];
        colorDsuParent[curr] = root;
        curr = nxt;
    }
    return root;
}

static inline void colorDsuUnion(int u, int v) {
    int rootU = colorDsuFind(u);
    int rootV = colorDsuFind(v);
    if (rootU != rootV) {
        if (colorDsuRank[rootU] < colorDsuRank[rootV]) {
            colorDsuParent[rootU] = rootV;
        } else if (colorDsuRank[rootU] > colorDsuRank[rootV]) {
            colorDsuParent[rootV] = rootU;
        } else {
            colorDsuParent[rootU] = rootV;
            colorDsuRank[rootV]++;
        }
    }
}

static bool applyInsideOutsideColoring() {
    int numCells = rows * cols;
    int outsideCell = numCells;
    int totalNodes = outsideCell + 1;
    
    // Bipartite DSU: node i is Color A, node i + totalNodes is Color B
    colorDsuInit(totalNodes * 2);
    
    // 1. Build relationships from edge states
    for (int e = 0; e < numEdges; e++) {
        if (edgeStates[e] == 0) continue;
        
        int cell1, cell2;
        if (e < numH) {
            int r = e / cols;
            int c = e % cols;
            cell1 = (r > 0) ? (r - 1) * cols + c : outsideCell;
            cell2 = (r < rows) ? r * cols + c : outsideCell;
        } else {
            int vIdx = e - numH;
            int r = vIdx / (cols + 1);
            int c = vIdx % (cols + 1);
            cell1 = (c > 0) ? r * cols + (c - 1) : outsideCell;
            cell2 = (c < cols) ? r * cols + c : outsideCell;
        }
        
        if (edgeStates[e] == -1) {
            // Cross -> Same color
            colorDsuUnion(cell1, cell2);
            colorDsuUnion(cell1 + totalNodes, cell2 + totalNodes);
        } else if (edgeStates[e] == 1) {
            // Line -> Different color
            colorDsuUnion(cell1, cell2 + totalNodes);
            colorDsuUnion(cell1 + totalNodes, cell2);
        }
        
        // Contradiction check
        if (colorDsuFind(cell1) == colorDsuFind(cell1 + totalNodes)) return false;
        if (colorDsuFind(cell2) == colorDsuFind(cell2 + totalNodes)) return false;
    }
    
    // 2. Resolve undecided edges
    for (int e = 0; e < numEdges; e++) {
        if (edgeStates[e] != 0) continue;
        
        int cell1, cell2;
        if (e < numH) {
            int r = e / cols;
            int c = e % cols;
            cell1 = (r > 0) ? (r - 1) * cols + c : outsideCell;
            cell2 = (r < rows) ? r * cols + c : outsideCell;
        } else {
            int vIdx = e - numH;
            int r = vIdx / (cols + 1);
            int c = vIdx % (cols + 1);
            cell1 = (c > 0) ? r * cols + (c - 1) : outsideCell;
            cell2 = (c < cols) ? r * cols + c : outsideCell;
        }
        
        if (colorDsuFind(cell1) == colorDsuFind(cell2)) {
            // Must be same color -> MUST be cross
            if (!setEdgeState(e, -1)) return false;
        } else if (colorDsuFind(cell1) == colorDsuFind(cell2 + totalNodes)) {
            // Must be different color -> MUST be line
            if (!setEdgeState(e, 1)) return false;
        }
    }
    
    return true;
}

static bool applyVirtualPathLogic() {
    bool changed = false;
    
    int forbiddenA[400];
    int forbiddenB[400];
    int forbiddenE1[400];
    int forbiddenE2[400];
    int forbiddenCount = 0;
    
    for (int r = 0; r < rows; r++) {
        for (int c = 0; c < cols; c++) {
            int clue = clues[r * cols + c];
            if (clue == -1) continue;
            
            int edges[4];
            edges[0] = getHEdgeIndex(r, c);       // Top
            edges[1] = getHEdgeIndex(r + 1, c);   // Bottom
            edges[2] = getVEdgeIndex(r, c);       // Left
            edges[3] = getVEdgeIndex(r, c + 1);   // Right
            
            int lines = 0, crosses = 0;
            int undecided[4];
            int undecidedCount = 0;
            
            for (int i = 0; i < 4; i++) {
                if (edges[i] == -1) continue; 
                if (edgeStates[edges[i]] == 1) lines++;
                else if (edgeStates[edges[i]] == -1) crosses++;
                else undecided[undecidedCount++] = edges[i];
            }
            
            if (lines + 1 == clue && undecidedCount == 2) {
                int e1 = undecided[0];
                int e2 = undecided[1];
                
                int u1, v1, u2, v2;
                if (e1 < numH) {
                    u1 = (e1 / cols) * (cols + 1) + (e1 % cols); v1 = u1 + 1;
                } else {
                    int vIdx = e1 - numH;
                    u1 = (vIdx / (cols + 1)) * (cols + 1) + (vIdx % (cols + 1)); v1 = u1 + (cols + 1);
                }
                if (e2 < numH) {
                    u2 = (e2 / cols) * (cols + 1) + (e2 % cols); v2 = u2 + 1;
                } else {
                    int vIdx = e2 - numH;
                    u2 = (vIdx / (cols + 1)) * (cols + 1) + (vIdx % (cols + 1)); v2 = u2 + (cols + 1);
                }
                
                int shared_dot = -1, other1 = -1, other2 = -1;
                if (u1 == u2) { shared_dot = u1; other1 = v1; other2 = v2; }
                else if (u1 == v2) { shared_dot = u1; other1 = v1; other2 = u2; }
                else if (v1 == u2) { shared_dot = v1; other1 = u1; other2 = v2; }
                else if (v1 == v2) { shared_dot = v1; other1 = u1; other2 = u2; }
                
                if (shared_dot != -1) {
                    if (dsuFind(other1) == dsuFind(other2)) {
                        int compA = dsuFind(other1);
                        int compB = dsuFind(shared_dot);
                        if (compA == compB) {
                            return false; 
                        } else {
                            forbiddenA[forbiddenCount] = compA;
                            forbiddenB[forbiddenCount] = compB;
                            forbiddenE1[forbiddenCount] = e1;
                            forbiddenE2[forbiddenCount] = e2;
                            forbiddenCount++;
                        }
                    }
                }
            }
        }
    }
    
    if (forbiddenCount > 0) {
        for (int k = 0; k < numEdges; k++) {
            if (edgeStates[k] == 0) {
                int uk, vk;
                if (k < numH) {
                    uk = (k / cols) * (cols + 1) + (k % cols); vk = uk + 1;
                } else {
                    int vIdx = k - numH;
                    uk = (vIdx / (cols + 1)) * (cols + 1) + (vIdx % (cols + 1)); vk = uk + (cols + 1);
                }
                int compU = dsuFind(uk);
                int compV = dsuFind(vk);
                
                for (int i = 0; i < forbiddenCount; i++) {
                    if (k == forbiddenE1[i] || k == forbiddenE2[i]) continue;
                    
                    int fA = forbiddenA[i];
                    int fB = forbiddenB[i];
                    if ((compU == fA && compV == fB) || (compU == fB && compV == fA)) {
                        // Check if it's the valid final loop before banning
                        edgeStates[k] = 1;
                        edgeStates[forbiddenE1[i]] = 1;
                        edgeStates[forbiddenE2[i]] = -1;
                        bool solved1 = isSolved();
                        
                        edgeStates[forbiddenE1[i]] = -1;
                        edgeStates[forbiddenE2[i]] = 1;
                        bool solved2 = isSolved();
                        
                        edgeStates[k] = 0;
                        edgeStates[forbiddenE1[i]] = 0;
                        edgeStates[forbiddenE2[i]] = 0;
                        
                        if (!solved1 && !solved2) {
                            if (!setEdgeState(k, -1)) return false;
                            changed = true;
                        }
                    }
                }
            }
        }
    }
    
    if (changed) {
        for(int r=0; r<rows; r++) {
            for(int c=0; c<cols; c++) cellStack[cellStackTop++] = r * cols + c;
        }
        for(int r=0; r<=rows; r++) {
            for(int c=0; c<=cols; c++) dotStack[dotStackTop++] = r * (cols + 1) + c;
        }
    }
    return true;
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
    
    while (true) {
        // 1. 手前側の角(XORが到達した角)のエッジを取得する
        int inEdge1 = numEdges, inEdge2 = numEdges;
        if (dr == 1 && dc == 1) { // 進行方向が右下 -> 手前は左上
            inEdge1 = getHEdgeIndex(curr_r, curr_c);
            inEdge2 = getVEdgeIndex(curr_r, curr_c);
        } else if (dr == -1 && dc == -1) { // 左上へ -> 手前は右下
            inEdge1 = getHEdgeIndex(curr_r + 1, curr_c);
            inEdge2 = getVEdgeIndex(curr_r, curr_c + 1);
        } else if (dr == -1 && dc == 1) { // 右上へ -> 手前は左下
            inEdge1 = getHEdgeIndex(curr_r + 1, curr_c);
            inEdge2 = getVEdgeIndex(curr_r, curr_c);
        } else if (dr == 1 && dc == -1) { // 左下へ -> 手前は右上
            inEdge1 = getHEdgeIndex(curr_r, curr_c);
            inEdge2 = getVEdgeIndex(curr_r, curr_c + 1);
        }
        
        // 2. XOR制約の伝搬 (到達した角は「1本貫通」状態のはずなので、片方が確定していればもう一方を確定)
        if (inEdge1 != numEdges && inEdge2 != numEdges) {
            if (edgeStates[inEdge1] == 1) { if (!setEdgeState(inEdge2, -1)) return false; }
            if (edgeStates[inEdge1] == -1) { if (!setEdgeState(inEdge2, 1)) return false; }
            if (edgeStates[inEdge2] == 1) { if (!setEdgeState(inEdge1, -1)) return false; }
            if (edgeStates[inEdge2] == -1) { if (!setEdgeState(inEdge1, 1)) return false; }
        } else if (inEdge1 != numEdges && inEdge2 == numEdges) {
            // 盤面の端で片方のエッジしか存在しない場合、もう一方は必ず線になる
            if (!setEdgeState(inEdge1, 1)) return false;
        } else if (inEdge1 == numEdges && inEdge2 != numEdges) {
            // 盤面の端で片方のエッジしか存在しない場合、もう一方は必ず線になる
            if (!setEdgeState(inEdge2, 1)) return false;
        } else {
            // 完全に盤面外（四隅の外）なら矛盾
            return false;
        }
        
        if (curr_r < 0 || curr_r >= rows || curr_c < 0 || curr_c >= cols) break;
        
        int clue = getClue(curr_r, curr_c);
        
        if (clue == 2) {
            // 2のセルの場合、対角の角もXOR状態となり、次のセルへ伝搬する
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

            if (oppEdge1 != -1 && oppEdge2 != -1) {
                if (edgeStates[oppEdge1] == 1) { if (!setEdgeState(oppEdge2, -1)) return false; }
                if (edgeStates[oppEdge1] == -1) { if (!setEdgeState(oppEdge2, 1)) return false; }
                if (edgeStates[oppEdge2] == 1) { if (!setEdgeState(oppEdge1, -1)) return false; }
                if (edgeStates[oppEdge2] == -1) { if (!setEdgeState(oppEdge1, 1)) return false; }
            }

            curr_r += dr;
            curr_c += dc;
        } else {
            // 2以外のセルに到達した場合、伝搬はここで終了。
            // さらに奥側の角に対する特殊な推論（1や3の場合）を行う。
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
                return false; // 手前角にXOR(線1本入る)が確定しているのに0セルは矛盾
            } else if (clue == 1) {
                if (oppEdge1 != -1 && !setEdgeState(oppEdge1, -1)) return false;
                if (oppEdge2 != -1 && !setEdgeState(oppEdge2, -1)) return false;
            } else if (clue == 3) {
                if (oppEdge1 != -1 && !setEdgeState(oppEdge1, 1)) return false;
                if (oppEdge2 != -1 && !setEdgeState(oppEdge2, 1)) return false;
            }
            break;
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



static inline bool deductIncremental_internal() {
    ac3_current_rule_id = -1;
    ac3_t_start = emscripten_get_now();
    int loopCount = 0;
    while (true) {
        loopCount++;
        if (loopCount > 10000) {
            printf("[C ERROR] deductIncremental infinite loop detected! stack sizes: cells=%d, dots=%d\n", 
                   cellStackTop, dotStackTop);
            AC3_RETURN_FALSE; // Force stop
        }
        while (cellStackTop > 0 || dotStackTop > 0) {
            if (isDoingLookahead && lookaheadMaxLimit > 0 && lookaheadConfirmedCount >= lookaheadMaxLimit) {
                cellStackTop = 0;
                dotStackTop = 0;
                AC3_RETURN_TRUE;
            }
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
                    if (ac3_current_difficulty_limit >= DIFF_MEDIUM) {
                        RECORD_AC3_TIME(121);
                        if (!check23CornerLogic(r, c)) AC3_RETURN_FALSE;
                        if (!check22CornerLogic(r, c)) AC3_RETURN_FALSE;
                    }
                    
                    int cellEdges[4];
                    getCellEdges(r, c, cellEdges);
                    
                    if (ac3_current_difficulty_limit >= DIFF_BASIC) {
                        RECORD_AC3_TIME(101);
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
                            AC3_RETURN_FALSE; // Contradiction
                        }
                        
                        if (undecidedCount > 0) {
                            if (lines == clue) {
                                for (int j = 0; j < undecidedCount; j++) {
                                    if (!setEdgeState(undecided[j], -1)) AC3_RETURN_FALSE;
                                }
                            } else if (crosses == (4 - clue)) {
                                for (int j = 0; j < undecidedCount; j++) {
                                    if (!setEdgeState(undecided[j], 1)) AC3_RETURN_FALSE;
                                }
                            }
                        }
                    }
                    
                    if (clue == 3 && ac3_current_difficulty_limit >= DIFF_HARD) {
                        RECORD_AC3_TIME(131);
                        int eT = cellEdges[0];
                        int eR = cellEdges[1];
                        int eB = cellEdges[2];
                        int eL = cellEdges[3];
                        // Early SLE for Clue 3
                        if (edgeStates[eT] == 1 && edgeStates[eL] == 1) { if (!propagateDiagonal2s(r + 1, c + 1, 1, 1)) AC3_RETURN_FALSE; }
                        if (edgeStates[eT] == 1 && edgeStates[eR] == 1) { if (!propagateDiagonal2s(r + 1, c - 1, 1, -1)) AC3_RETURN_FALSE; }
                        if (edgeStates[eB] == 1 && edgeStates[eL] == 1) { if (!propagateDiagonal2s(r - 1, c + 1, -1, 1)) AC3_RETURN_FALSE; }
                        if (edgeStates[eB] == 1 && edgeStates[eR] == 1) { if (!propagateDiagonal2s(r - 1, c - 1, -1, -1)) AC3_RETURN_FALSE; }
                        
                        int status;
                        // Down-Right dot is eB, eR. Opposite is eT, eL.
                        status = checkDiagonalChain(clue, r, c, 1, 1);
                        if (status & 1) { if (!setEdgeState(eT, 1)) AC3_RETURN_FALSE; if (!setEdgeState(eL, 1)) AC3_RETURN_FALSE; }
                        if (status & 2) { if (!setEdgeState(eB, 1)) AC3_RETURN_FALSE; if (!setEdgeState(eR, 1)) AC3_RETURN_FALSE; }
                        // Down-Left dot is eB, eL. Opposite is eT, eR.
                        status = checkDiagonalChain(clue, r, c, 1, -1);
                        if (status & 1) { if (!setEdgeState(eT, 1)) AC3_RETURN_FALSE; if (!setEdgeState(eR, 1)) AC3_RETURN_FALSE; }
                        if (status & 2) { if (!setEdgeState(eB, 1)) AC3_RETURN_FALSE; if (!setEdgeState(eL, 1)) AC3_RETURN_FALSE; }
                        // Up-Right dot is eT, eR. Opposite is eB, eL.
                        status = checkDiagonalChain(clue, r, c, -1, 1);
                        if (status & 1) { if (!setEdgeState(eB, 1)) AC3_RETURN_FALSE; if (!setEdgeState(eL, 1)) AC3_RETURN_FALSE; }
                        if (status & 2) { if (!setEdgeState(eT, 1)) AC3_RETURN_FALSE; if (!setEdgeState(eR, 1)) AC3_RETURN_FALSE; }
                        // Up-Left dot is eT, eL. Opposite is eB, eR.
                        status = checkDiagonalChain(clue, r, c, -1, -1);
                        if (status & 1) { if (!setEdgeState(eB, 1)) AC3_RETURN_FALSE; if (!setEdgeState(eR, 1)) AC3_RETURN_FALSE; }
                        if (status & 2) { if (!setEdgeState(eT, 1)) AC3_RETURN_FALSE; if (!setEdgeState(eL, 1)) AC3_RETURN_FALSE; }

                    } else if (clue == 1 && ac3_current_difficulty_limit >= DIFF_MEDIUM) {
                        RECORD_AC3_TIME(122);
                        int eT = cellEdges[0];
                        int eR = cellEdges[1];
                        int eB = cellEdges[2];
                        int eL = cellEdges[3];
                        // Early SLE for Clue 1
                        if (edgeStates[eT] == -1 && edgeStates[eL] == -1) { if (!propagateDiagonal2s(r + 1, c + 1, 1, 1)) AC3_RETURN_FALSE; }
                        if (edgeStates[eT] == -1 && edgeStates[eR] == -1) { if (!propagateDiagonal2s(r + 1, c - 1, 1, -1)) AC3_RETURN_FALSE; }
                        if (edgeStates[eB] == -1 && edgeStates[eL] == -1) { if (!propagateDiagonal2s(r - 1, c + 1, -1, 1)) AC3_RETURN_FALSE; }
                        if (edgeStates[eB] == -1 && edgeStates[eR] == -1) { if (!propagateDiagonal2s(r - 1, c - 1, -1, -1)) AC3_RETURN_FALSE; }
                        
                        int status;
                        // Down-Right dot is eB, eR. Opposite is eT, eL.
                        status = checkDiagonalChain(clue, r, c, 1, 1);
                        if (status & 1) { if (!setEdgeState(eT, -1)) AC3_RETURN_FALSE; if (!setEdgeState(eL, -1)) AC3_RETURN_FALSE; }
                        if (status & 2) { if (!setEdgeState(eB, -1)) AC3_RETURN_FALSE; if (!setEdgeState(eR, -1)) AC3_RETURN_FALSE; }
                        // Down-Left dot is eB, eL. Opposite is eT, eR.
                        status = checkDiagonalChain(clue, r, c, 1, -1);
                        if (status & 1) { if (!setEdgeState(eT, -1)) AC3_RETURN_FALSE; if (!setEdgeState(eR, -1)) AC3_RETURN_FALSE; }
                        if (status & 2) { if (!setEdgeState(eB, -1)) AC3_RETURN_FALSE; if (!setEdgeState(eL, -1)) AC3_RETURN_FALSE; }
                        // Up-Right dot is eT, eR. Opposite is eB, eL.
                        status = checkDiagonalChain(clue, r, c, -1, 1);
                        if (status & 1) { if (!setEdgeState(eB, -1)) AC3_RETURN_FALSE; if (!setEdgeState(eL, -1)) AC3_RETURN_FALSE; }
                        if (status & 2) { if (!setEdgeState(eT, -1)) AC3_RETURN_FALSE; if (!setEdgeState(eR, -1)) AC3_RETURN_FALSE; }
                        // Up-Left dot is eT, eL. Opposite is eB, eR.
                        status = checkDiagonalChain(clue, r, c, -1, -1);
                        if (status & 1) { if (!setEdgeState(eB, -1)) AC3_RETURN_FALSE; if (!setEdgeState(eR, -1)) AC3_RETURN_FALSE; }
                        if (status & 2) { if (!setEdgeState(eT, -1)) AC3_RETURN_FALSE; if (!setEdgeState(eL, -1)) AC3_RETURN_FALSE; }

                    } else if (clue == 2) {
                        int eT = cellEdges[0];
                        int eR = cellEdges[1];
                        int eB = cellEdges[2];
                        int eL = cellEdges[3];
                        
                        if (ac3_current_difficulty_limit >= DIFF_MEDIUM) {
                            int stT = edgeStates[eT];
                            int stR = edgeStates[eR];
                            int stB = edgeStates[eB];
                            int stL = edgeStates[eL];
                            // General 2-cell XOR Propagation
                            // Check internal edges
                            if (stT != 0 && stL != 0 && stT != stL) { // Top-Left is XOR
                                RECORD_AC3_TIME(125);
                                if (stB == 1) { if (!setEdgeState(eR, -1)) AC3_RETURN_FALSE; }
                                if (stB == -1) { if (!setEdgeState(eR, 1)) AC3_RETURN_FALSE; }
                                if (stR == 1) { if (!setEdgeState(eB, -1)) AC3_RETURN_FALSE; }
                                if (stR == -1) { if (!setEdgeState(eB, 1)) AC3_RETURN_FALSE; }
                            }
                            if (stB != 0 && stR != 0 && stB != stR) { // Bottom-Right is XOR
                                RECORD_AC3_TIME(125);
                                if (stT == 1) { if (!setEdgeState(eL, -1)) AC3_RETURN_FALSE; }
                                if (stT == -1) { if (!setEdgeState(eL, 1)) AC3_RETURN_FALSE; }
                                if (stL == 1) { if (!setEdgeState(eT, -1)) AC3_RETURN_FALSE; }
                                if (stL == -1) { if (!setEdgeState(eT, 1)) AC3_RETURN_FALSE; }
                            }
                            if (stT != 0 && stR != 0 && stT != stR) { // Top-Right is XOR
                                RECORD_AC3_TIME(125);
                                if (stB == 1) { if (!setEdgeState(eL, -1)) AC3_RETURN_FALSE; }
                                if (stB == -1) { if (!setEdgeState(eL, 1)) AC3_RETURN_FALSE; }
                                if (stL == 1) { if (!setEdgeState(eB, -1)) AC3_RETURN_FALSE; }
                                if (stL == -1) { if (!setEdgeState(eB, 1)) AC3_RETURN_FALSE; }
                            }
                            if (stB != 0 && stL != 0 && stB != stL) { // Bottom-Left is XOR
                                RECORD_AC3_TIME(125);
                                if (stT == 1) { if (!setEdgeState(eR, -1)) AC3_RETURN_FALSE; }
                                if (stT == -1) { if (!setEdgeState(eR, 1)) AC3_RETURN_FALSE; }
                                if (stR == 1) { if (!setEdgeState(eT, -1)) AC3_RETURN_FALSE; }
                                if (stR == -1) { if (!setEdgeState(eT, 1)) AC3_RETURN_FALSE; }
                            }

                            // Check outside edges (incoming line to a corner of 2)
                            int outT_L = getHEdgeIndex(r, c - 1);
                            int outL_T = getVEdgeIndex(r - 1, c);
                            int stT_L = (outT_L == numEdges) ? -1 : edgeStates[outT_L];
                            int stL_T = (outL_T == numEdges) ? -1 : edgeStates[outL_T];
                            if (stT_L != 0 && stL_T != 0 && stT_L != stL_T) {
                                RECORD_AC3_TIME(125);
                                if (!propagateDiagonal2s(r, c, 1, 1)) AC3_RETURN_FALSE;
                            }
                            int outT_R = getHEdgeIndex(r, c + 1);
                            int outR_T = getVEdgeIndex(r - 1, c + 1);
                            int stT_R = (outT_R == numEdges) ? -1 : edgeStates[outT_R];
                            int stR_T = (outR_T == numEdges) ? -1 : edgeStates[outR_T];
                            if (stT_R != 0 && stR_T != 0 && stT_R != stR_T) {
                                RECORD_AC3_TIME(125);
                                if (!propagateDiagonal2s(r, c, 1, -1)) AC3_RETURN_FALSE;
                            }
                            int outB_L = getHEdgeIndex(r + 1, c - 1);
                            int outL_B = getVEdgeIndex(r + 1, c);
                            int stB_L = (outB_L == numEdges) ? -1 : edgeStates[outB_L];
                            int stL_B = (outL_B == numEdges) ? -1 : edgeStates[outL_B];
                            if (stB_L != 0 && stL_B != 0 && stB_L != stL_B) {
                                RECORD_AC3_TIME(125);
                                if (!propagateDiagonal2s(r, c, -1, 1)) AC3_RETURN_FALSE;
                            }
                            int outB_R = getHEdgeIndex(r + 1, c + 1);
                            int outR_B = getVEdgeIndex(r + 1, c + 1);
                            int stB_R = (outB_R == numEdges) ? -1 : edgeStates[outB_R];
                            int stR_B = (outR_B == numEdges) ? -1 : edgeStates[outR_B];
                            if (stB_R != 0 && stR_B != 0 && stB_R != stR_B) {
                                RECORD_AC3_TIME(125);
                                if (!propagateDiagonal2s(r, c, -1, -1)) AC3_RETURN_FALSE;
                            }
                        }

                        if (ac3_current_difficulty_limit >= DIFF_HARD) {
                            RECORD_AC3_TIME(136);
                            // Early SLE for Clue 2 (User's observation)
                        // Top-Left Dot Outside Edges: H(r, c-1) and V(r-1, c)
                        int outT_L = getHEdgeIndex(r, c - 1);
                        int outL_T = getVEdgeIndex(r - 1, c);
                        if (outT_L != -1 && outL_T != -1 && edgeStates[outT_L] != 0 && edgeStates[outT_L] == edgeStates[outL_T]) {
                            if (!propagateDiagonal2s(r - 1, c + 1, -1, 1)) AC3_RETURN_FALSE; // Up-Right
                            if (!propagateDiagonal2s(r + 1, c - 1, 1, -1)) AC3_RETURN_FALSE; // Down-Left
                        }
                        // Top-Right Dot Outside Edges: H(r, c+1) and V(r-1, c+1)
                        int outT_R = getHEdgeIndex(r, c + 1);
                        int outR_T = getVEdgeIndex(r - 1, c + 1);
                        if (outT_R != -1 && outR_T != -1 && edgeStates[outT_R] != 0 && edgeStates[outT_R] == edgeStates[outR_T]) {
                            if (!propagateDiagonal2s(r - 1, c - 1, -1, -1)) AC3_RETURN_FALSE; // Up-Left
                            if (!propagateDiagonal2s(r + 1, c + 1, 1, 1)) AC3_RETURN_FALSE;   // Down-Right
                        }
                        // Bottom-Left Dot Outside Edges: H(r+1, c-1) and V(r+1, c)
                        int outB_L = getHEdgeIndex(r + 1, c - 1);
                        int outL_B = getVEdgeIndex(r + 1, c);
                        if (outB_L != -1 && outL_B != -1 && edgeStates[outB_L] != 0 && edgeStates[outB_L] == edgeStates[outL_B]) {
                            if (!propagateDiagonal2s(r - 1, c - 1, -1, -1)) AC3_RETURN_FALSE; // Up-Left
                            if (!propagateDiagonal2s(r + 1, c + 1, 1, 1)) AC3_RETURN_FALSE;   // Down-Right
                        }
                        // Bottom-Right Dot Outside Edges: H(r+1, c+1) and V(r+1, c+1)
                        int outB_R = getHEdgeIndex(r + 1, c + 1);
                        int outR_B = getVEdgeIndex(r + 1, c + 1);
                        if (outB_R != -1 && outR_B != -1 && edgeStates[outB_R] != 0 && edgeStates[outB_R] == edgeStates[outR_B]) {
                            if (!propagateDiagonal2s(r - 1, c + 1, -1, 1)) AC3_RETURN_FALSE; // Up-Right
                            if (!propagateDiagonal2s(r + 1, c - 1, 1, -1)) AC3_RETURN_FALSE; // Down-Left
                        }
                    }
                    
                    if (ac3_current_difficulty_limit >= DIFF_EASY) {
                            // "2の対角両端に進入する線がある場合、もう片方の外側エッジは×になる"
                            int outT_L = getHEdgeIndex(r, c - 1);
                            int outL_T = getVEdgeIndex(r - 1, c);
                            int outB_R = getHEdgeIndex(r + 1, c + 1);
                            int outR_B = getVEdgeIndex(r + 1, c + 1);
                            
                            if ((edgeStates[outT_L] == 1 || edgeStates[outL_T] == 1) &&
                                (edgeStates[outB_R] == 1 || edgeStates[outR_B] == 1)) {
                                
                                int prev_rule_id = ac3_current_rule_id;
RECORD_AC3_TIME(115);
                                ac3_current_rule_id = 115;
                                
                                if (edgeStates[outT_L] == 1) { if (!setEdgeState(outL_T, -1)) AC3_RETURN_FALSE; }
                                if (edgeStates[outL_T] == 1) { if (!setEdgeState(outT_L, -1)) AC3_RETURN_FALSE; }
                                if (edgeStates[outB_R] == 1) { if (!setEdgeState(outR_B, -1)) AC3_RETURN_FALSE; }
                                if (edgeStates[outR_B] == 1) { if (!setEdgeState(outB_R, -1)) AC3_RETURN_FALSE; }
                                
                                ac3_current_rule_id = prev_rule_id;
                                RECORD_AC3_TIME(prev_rule_id);
                            }
                            
                            int outT_R = getHEdgeIndex(r, c + 1);
                            int outR_T = getVEdgeIndex(r - 1, c + 1);
                            int outB_L = getHEdgeIndex(r + 1, c - 1);
                            int outL_B = getVEdgeIndex(r + 1, c);
                            
                            if ((edgeStates[outT_R] == 1 || edgeStates[outR_T] == 1) &&
                                (edgeStates[outB_L] == 1 || edgeStates[outL_B] == 1)) {
                                
                                int prev_rule_id = ac3_current_rule_id;
RECORD_AC3_TIME(115);
                                ac3_current_rule_id = 115;
                                
                                if (edgeStates[outT_R] == 1) { if (!setEdgeState(outR_T, -1)) AC3_RETURN_FALSE; }
                                if (edgeStates[outR_T] == 1) { if (!setEdgeState(outT_R, -1)) AC3_RETURN_FALSE; }
                                if (edgeStates[outB_L] == 1) { if (!setEdgeState(outL_B, -1)) AC3_RETURN_FALSE; }
                                if (edgeStates[outL_B] == 1) { if (!setEdgeState(outB_L, -1)) AC3_RETURN_FALSE; }
                                
                                ac3_current_rule_id = prev_rule_id;
                                RECORD_AC3_TIME(prev_rule_id);
                            }
                        }
                    }
                    
                    // Universal SLE Propagation
                    if (ac3_current_difficulty_limit >= DIFF_MEDIUM) {
                        RECORD_AC3_TIME(124);
                        // If any corner has exactly 1 line and 1 cross, it shoots an SLE diagonally.
                    int eT = cellEdges[0];
                    int eR = cellEdges[1];
                    int eB = cellEdges[2];
                    int eL = cellEdges[3];
                    if (edgeStates[eT] != 0 && edgeStates[eL] != 0 && edgeStates[eT] != edgeStates[eL]) {
                        if (!propagateDiagonal2s(r - 1, c - 1, -1, -1)) AC3_RETURN_FALSE;
                        if (clue == 2 && (edgeStates[eB] == 0 || edgeStates[eR] == 0)) {
                            if (!propagateDiagonal2s(r + 1, c + 1, 1, 1)) AC3_RETURN_FALSE;
                        }
                    }
                    if (edgeStates[eT] != 0 && edgeStates[eR] != 0 && edgeStates[eT] != edgeStates[eR]) {
                        if (!propagateDiagonal2s(r - 1, c + 1, -1, 1)) AC3_RETURN_FALSE;
                        if (clue == 2 && (edgeStates[eB] == 0 || edgeStates[eL] == 0)) {
                            if (!propagateDiagonal2s(r + 1, c - 1, 1, -1)) AC3_RETURN_FALSE;
                        }
                    }
                    if (edgeStates[eB] != 0 && edgeStates[eL] != 0 && edgeStates[eB] != edgeStates[eL]) {
                        if (!propagateDiagonal2s(r + 1, c - 1, 1, -1)) AC3_RETURN_FALSE;
                        if (clue == 2 && (edgeStates[eT] == 0 || edgeStates[eR] == 0)) {
                            if (!propagateDiagonal2s(r - 1, c + 1, -1, 1)) AC3_RETURN_FALSE;
                        }
                    }
                    if (edgeStates[eB] != 0 && edgeStates[eR] != 0 && edgeStates[eB] != edgeStates[eR]) {
                        if (!propagateDiagonal2s(r + 1, c + 1, 1, 1)) AC3_RETURN_FALSE;
                        if (clue == 2 && (edgeStates[eT] == 0 || edgeStates[eL] == 0)) {
                            if (!propagateDiagonal2s(r - 1, c - 1, -1, -1)) AC3_RETURN_FALSE;
                        }
                    }
                    }
                    if (clue == 2) {
                        if (ac3_current_difficulty_limit >= DIFF_HARD) {
                            RECORD_AC3_TIME(140);
                            int eT = cellEdges[0];
                            int eR = cellEdges[1];
                            int eB = cellEdges[2];
                            int eL = cellEdges[3];
                            // Check Top-Left diagonal for a 3
                            if (r > 0 && c > 0 && clues[(r-1)*cols + (c-1)] == 3) {
                                int outB_R = getHEdgeIndex(r+1, c+1);
                                int outR_B = getVEdgeIndex(r+1, c+1);
                                if (edgeStates[eB] == -1 || edgeStates[eR] == -1 || edgeStates[outB_R] == 1 || edgeStates[outR_B] == 1) {
                                    if (edgeStates[eB] == -1) { if (!setEdgeState(eR, 1)) AC3_RETURN_FALSE; }
                                    if (edgeStates[eR] == -1) { if (!setEdgeState(eB, 1)) AC3_RETURN_FALSE; }
                                    if (edgeStates[outB_R] == 1) { if (!setEdgeState(outR_B, -1)) AC3_RETURN_FALSE; }
                                    if (edgeStates[outR_B] == 1) { if (!setEdgeState(outB_R, -1)) AC3_RETURN_FALSE; }
                                    if (!setEdgeState(getHEdgeIndex(r-1, c-1), 1)) AC3_RETURN_FALSE;
                                    if (!setEdgeState(getVEdgeIndex(r-1, c-1), 1)) AC3_RETURN_FALSE;
                                }
                            }
                            // Check Top-Right diagonal for a 3
                            if (r > 0 && c < cols - 1 && clues[(r-1)*cols + (c+1)] == 3) {
                                int outB_L = getHEdgeIndex(r+1, c-1);
                                int outL_B = getVEdgeIndex(r+1, c);
                                if (edgeStates[eB] == -1 || edgeStates[eL] == -1 || edgeStates[outB_L] == 1 || edgeStates[outL_B] == 1) {
                                    if (edgeStates[eB] == -1) { if (!setEdgeState(eL, 1)) AC3_RETURN_FALSE; }
                                    if (edgeStates[eL] == -1) { if (!setEdgeState(eB, 1)) AC3_RETURN_FALSE; }
                                    if (edgeStates[outB_L] == 1) { if (!setEdgeState(outL_B, -1)) AC3_RETURN_FALSE; }
                                    if (edgeStates[outL_B] == 1) { if (!setEdgeState(outB_L, -1)) AC3_RETURN_FALSE; }
                                    if (!setEdgeState(getHEdgeIndex(r-1, c+1), 1)) AC3_RETURN_FALSE;
                                    if (!setEdgeState(getVEdgeIndex(r-1, c+2), 1)) AC3_RETURN_FALSE;
                                }
                            }
                            // Check Bottom-Left diagonal for a 3
                            if (r < rows - 1 && c > 0 && clues[(r+1)*cols + (c-1)] == 3) {
                                int outT_R = getHEdgeIndex(r, c+1);
                                int outR_T = getVEdgeIndex(r-1, c+1);
                                if (edgeStates[eT] == -1 || edgeStates[eR] == -1 || edgeStates[outT_R] == 1 || edgeStates[outR_T] == 1) {
                                    if (edgeStates[eT] == -1) { if (!setEdgeState(eR, 1)) AC3_RETURN_FALSE; }
                                    if (edgeStates[eR] == -1) { if (!setEdgeState(eT, 1)) AC3_RETURN_FALSE; }
                                    if (edgeStates[outT_R] == 1) { if (!setEdgeState(outR_T, -1)) AC3_RETURN_FALSE; }
                                    if (edgeStates[outR_T] == 1) { if (!setEdgeState(outT_R, -1)) AC3_RETURN_FALSE; }
                                    if (!setEdgeState(getHEdgeIndex(r+2, c-1), 1)) AC3_RETURN_FALSE;
                                    if (!setEdgeState(getVEdgeIndex(r+1, c-1), 1)) AC3_RETURN_FALSE;
                                }
                            }
                            // Check Bottom-Right diagonal for a 3
                            if (r < rows - 1 && c < cols - 1 && clues[(r+1)*cols + (c+1)] == 3) {
                                int outT_L = getHEdgeIndex(r, c-1);
                                int outL_T = getVEdgeIndex(r-1, c);
                                if (edgeStates[eT] == -1 || edgeStates[eL] == -1 || edgeStates[outT_L] == 1 || edgeStates[outL_T] == 1) {
                                    if (edgeStates[eT] == -1) { if (!setEdgeState(eL, 1)) AC3_RETURN_FALSE; }
                                    if (edgeStates[eL] == -1) { if (!setEdgeState(eT, 1)) AC3_RETURN_FALSE; }
                                    if (edgeStates[outT_L] == 1) { if (!setEdgeState(outL_T, -1)) AC3_RETURN_FALSE; }
                                    if (edgeStates[outL_T] == 1) { if (!setEdgeState(outT_L, -1)) AC3_RETURN_FALSE; }
                                    if (!setEdgeState(getHEdgeIndex(r+2, c+1), 1)) AC3_RETURN_FALSE;
                                    if (!setEdgeState(getVEdgeIndex(r+1, c+2), 1)) AC3_RETURN_FALSE;
                                }
                            }
                        }

                        if (ac3_current_difficulty_limit >= DIFF_HARD) {
                            RECORD_AC3_TIME(137);
                            // "2-chain to 1 or 3 with an external cross" deduction rule
                            
                            // Top-Left Dot Outside Edges: H(r, c-1) and V(r-1, c)
                            int outT_L = getHEdgeIndex(r, c - 1);
                            int outL_T = getVEdgeIndex(r - 1, c);
                            int stT_L = (outT_L == numEdges) ? -1 : edgeStates[outT_L];
                            int stL_T = (outL_T == numEdges) ? -1 : edgeStates[outL_T];
                            if (stT_L == -1 && stL_T == -1) {
                                int curr_r = r + 1, curr_c = c + 1;
                                while (getClue(curr_r, curr_c) == 2) { curr_r++; curr_c++; }
                                int endClue = getClue(curr_r, curr_c);
                                if (endClue == 1) {
                                    if (!setEdgeState(getHEdgeIndex(curr_r, curr_c), -1)) AC3_RETURN_FALSE;
                                    if (!setEdgeState(getVEdgeIndex(curr_r, curr_c), -1)) AC3_RETURN_FALSE;
                                } else if (endClue == 3) {
                                    if (!setEdgeState(getHEdgeIndex(r, c), 1)) AC3_RETURN_FALSE;
                                    if (!setEdgeState(getVEdgeIndex(r, c), 1)) AC3_RETURN_FALSE;
                                }
                            }
                            
                            // Top-Right Dot Outside Edges: H(r, c+1) and V(r-1, c+1)
                            int outT_R = getHEdgeIndex(r, c + 1);
                            int outR_T = getVEdgeIndex(r - 1, c + 1);
                            int stT_R = (outT_R == numEdges) ? -1 : edgeStates[outT_R];
                            int stR_T = (outR_T == numEdges) ? -1 : edgeStates[outR_T];
                            if (stT_R == -1 && stR_T == -1) {
                                int curr_r = r + 1, curr_c = c - 1;
                                while (getClue(curr_r, curr_c) == 2) { curr_r++; curr_c--; }
                                int endClue = getClue(curr_r, curr_c);
                                if (endClue == 1) {
                                    if (!setEdgeState(getHEdgeIndex(curr_r, curr_c), -1)) AC3_RETURN_FALSE;
                                    if (!setEdgeState(getVEdgeIndex(curr_r, curr_c + 1), -1)) AC3_RETURN_FALSE;
                                } else if (endClue == 3) {
                                    if (!setEdgeState(getHEdgeIndex(r, c), 1)) AC3_RETURN_FALSE;
                                    if (!setEdgeState(getVEdgeIndex(r, c + 1), 1)) AC3_RETURN_FALSE;
                                }
                            }
                            
                            // Bottom-Left Dot Outside Edges: H(r+1, c-1) and V(r+1, c)
                            int outB_L = getHEdgeIndex(r + 1, c - 1);
                            int outL_B = getVEdgeIndex(r + 1, c);
                            int stB_L = (outB_L == numEdges) ? -1 : edgeStates[outB_L];
                            int stL_B = (outL_B == numEdges) ? -1 : edgeStates[outL_B];
                            if (stB_L == -1 && stL_B == -1) {
                                int curr_r = r - 1, curr_c = c + 1;
                                while (getClue(curr_r, curr_c) == 2) { curr_r--; curr_c++; }
                                int endClue = getClue(curr_r, curr_c);
                                if (endClue == 1) {
                                    if (!setEdgeState(getHEdgeIndex(curr_r + 1, curr_c), -1)) AC3_RETURN_FALSE;
                                    if (!setEdgeState(getVEdgeIndex(curr_r, curr_c), -1)) AC3_RETURN_FALSE;
                                } else if (endClue == 3) {
                                    if (!setEdgeState(getHEdgeIndex(r + 1, c), 1)) AC3_RETURN_FALSE;
                                    if (!setEdgeState(getVEdgeIndex(r, c), 1)) AC3_RETURN_FALSE;
                                }
                            }
                            
                            // Bottom-Right Dot Outside Edges: H(r+1, c+1) and V(r+1, c+1)
                            int outB_R = getHEdgeIndex(r + 1, c + 1);
                            int outR_B = getVEdgeIndex(r + 1, c + 1);
                            int stB_R = (outB_R == numEdges) ? -1 : edgeStates[outB_R];
                            int stR_B = (outR_B == numEdges) ? -1 : edgeStates[outR_B];
                            if (stB_R == -1 && stR_B == -1) {
                                int curr_r = r - 1, curr_c = c - 1;
                                while (getClue(curr_r, curr_c) == 2) { curr_r--; curr_c--; }
                                int endClue = getClue(curr_r, curr_c);
                                if (endClue == 1) {
                                    if (!setEdgeState(getHEdgeIndex(curr_r + 1, curr_c), -1)) AC3_RETURN_FALSE;
                                    if (!setEdgeState(getVEdgeIndex(curr_r, curr_c + 1), -1)) AC3_RETURN_FALSE;
                                } else if (endClue == 3) {
                                    if (!setEdgeState(getHEdgeIndex(r + 1, c), 1)) AC3_RETURN_FALSE;
                                    if (!setEdgeState(getVEdgeIndex(r, c + 1), 1)) AC3_RETURN_FALSE;
                                }
                            }
                        }
                    }
                }
            }
            
            // 2. Process dots
            int dotIdx = popDot();
            if (dotIdx != -1) {
                RECORD_AC3_TIME(103);
                dbgSource = "dot";
                dbgDot = dotIdx;
                dbgCell = -1;
                int r = dotIdx / (cols + 1);
                int c = dotIdx % (cols + 1);
                
                // --- NEW GENERALIZED 1-1 / 1-3 DOT BORDER LOGIC ---
                if (enableAdvancedAC3) {
                    int prev_rule_id = ac3_current_rule_id;
RECORD_AC3_TIME(138);
                    ac3_current_rule_id = 138;
                    
                    bool res = checkDotBorderLogic(r, c);
                    
                    ac3_current_rule_id = prev_rule_id;
                    RECORD_AC3_TIME(prev_rule_id);
                    
                    if (!res) AC3_RETURN_FALSE;
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
                                    int prev_rule_id = ac3_current_rule_id;
RECORD_AC3_TIME(141);
                                    ac3_current_rule_id = 141; // Using the same ID as global premature loop, or create a new one. Let's use the global one for aggregation.
                                    
                                    bool res = setEdgeState(edgeIdx, -1);
                                    
                                    ac3_current_rule_id = prev_rule_id;
                                    RECORD_AC3_TIME(prev_rule_id);
                                    
                                    if (!res) AC3_RETURN_FALSE;
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
                    AC3_RETURN_FALSE; // Contradiction: degree limit exceeded
                }
                
                if (undecidedCount > 0) {
                    if (lines == 2) {
                        for (int j = 0; j < undecidedCount; j++) {
                            if (!setEdgeState(undecided[j], -1)) {
                                AC3_RETURN_FALSE;
                            }
                        }
                    } else if (lines == 1 && undecidedCount == 1) {
                        if (!setEdgeState(undecided[0], 1)) {
                            AC3_RETURN_FALSE;
                        }
                    } else if (lines == 0 && undecidedCount == 1) {
                        if (!setEdgeState(undecided[0], -1)) {
                            AC3_RETURN_FALSE;
                        }
                    } else if (lines == 0 && undecidedCount == 2) {
                        // Rule A: Generalized Corner Heuristic
                        if (ac3_current_difficulty_limit >= DIFF_EASY) {
                            int prev_rule_id = ac3_current_rule_id;
RECORD_AC3_TIME(126);
                            ac3_current_rule_id = 111;
                            
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
                                        if (!setEdgeState(e1, 1)) AC3_RETURN_FALSE;
                                        if (!setEdgeState(e2, 1)) AC3_RETURN_FALSE;
                                    } else if (clue == 1) {
                                        if (!setEdgeState(e1, -1)) AC3_RETURN_FALSE;
                                        if (!setEdgeState(e2, -1)) AC3_RETURN_FALSE;
                                    }
                                }
                            }
                            
                            ac3_current_rule_id = prev_rule_id;
                            RECORD_AC3_TIME(prev_rule_id);
                        }
                    }
                } else {
                    if (lines != 0 && lines != 2) {
                        AC3_RETURN_FALSE; // Contradiction: degree must be 0 or 2
                    }
                }

                // (No special corner dot rules needed here, left to cell logic)
                // 3. Advanced Rule: Line entering a 3 corner
                int eL = getHEdgeIndex(r, c - 1);
                int eR = getHEdgeIndex(r, c);
                int eT = getVEdgeIndex(r - 1, c);
                int eB = getVEdgeIndex(r, c);
                
                if (ac3_current_difficulty_limit >= DIFF_HARD) {
                    RECORD_AC3_TIME(134);
                
                // Bottom-Right cell (cr=r, cc=c)
                if (getClue(r, c) == 3) {
                    if ((edgeStates[eL] == 1) || (edgeStates[eT] == 1)) {
                        if (edgeStates[eL] != 1) { if (!setEdgeState(eL, -1)) AC3_RETURN_FALSE; }
                        if (edgeStates[eT] != 1) { if (!setEdgeState(eT, -1)) AC3_RETURN_FALSE; }
                        if (!setEdgeState(getHEdgeIndex(r + 1, c), 1)) AC3_RETURN_FALSE;
                        if (!setEdgeState(getVEdgeIndex(r, c + 1), 1)) AC3_RETURN_FALSE;
                    }
                }
                // Bottom-Left cell (cr=r, cc=c-1)
                if (getClue(r, c - 1) == 3) {
                    if ((edgeStates[eR] == 1) || (edgeStates[eT] == 1)) {
                        if (edgeStates[eR] != 1) { if (!setEdgeState(eR, -1)) AC3_RETURN_FALSE; }
                        if (edgeStates[eT] != 1) { if (!setEdgeState(eT, -1)) AC3_RETURN_FALSE; }
                        if (!setEdgeState(getHEdgeIndex(r + 1, c - 1), 1)) AC3_RETURN_FALSE;
                        if (!setEdgeState(getVEdgeIndex(r, c - 1), 1)) AC3_RETURN_FALSE;
                    }
                }
                // Top-Right cell (cr=r-1, cc=c)
                if (getClue(r - 1, c) == 3) {
                    if ((edgeStates[eL] == 1) || (edgeStates[eB] == 1)) {
                        if (edgeStates[eL] != 1) { if (!setEdgeState(eL, -1)) AC3_RETURN_FALSE; }
                        if (edgeStates[eB] != 1) { if (!setEdgeState(eB, -1)) AC3_RETURN_FALSE; }
                        if (!setEdgeState(getHEdgeIndex(r - 1, c), 1)) AC3_RETURN_FALSE;
                        if (!setEdgeState(getVEdgeIndex(r - 1, c + 1), 1)) AC3_RETURN_FALSE;
                    }
                }
                // Top-Left cell (cr=r-1, cc=c-1)
                if (getClue(r - 1, c - 1) == 3) {
                    if ((edgeStates[eR] == 1) || (edgeStates[eB] == 1)) {
                        if (edgeStates[eR] != 1) { if (!setEdgeState(eR, -1)) AC3_RETURN_FALSE; }
                        if (edgeStates[eB] != 1) { if (!setEdgeState(eB, -1)) AC3_RETURN_FALSE; }
                        if (!setEdgeState(getHEdgeIndex(r - 1, c - 1), 1)) AC3_RETURN_FALSE;
                        if (!setEdgeState(getVEdgeIndex(r - 1, c - 1), 1)) AC3_RETURN_FALSE;
                    }
                }
                }
                
                // 4. Generalized Rule: Line entering a 2 corner with opposite known
                if (ac3_current_difficulty_limit >= DIFF_HARD) {
                    RECORD_AC3_TIME(133);
                    // Bottom-Right cell (cr=r, cc=c)
                if (getClue(r, c) == 2) {
                    bool entered = (edgeStates[eL] == 1 && edgeStates[eT] == -1) || (edgeStates[eL] == -1 && edgeStates[eT] == 1);
                    bool entering_possible = (edgeStates[eL] == 1 && edgeStates[eT] == 0) || (edgeStates[eL] == 0 && edgeStates[eT] == 1);
                    int oppB = getHEdgeIndex(r + 1, c);
                    int oppR = getVEdgeIndex(r, c + 1);
                    if (entering_possible && (edgeStates[oppB] == -1 || edgeStates[oppR] == -1)) {
                        if (edgeStates[eL] != 1) { if (!setEdgeState(eL, -1)) AC3_RETURN_FALSE; }
                        if (edgeStates[eT] != 1) { if (!setEdgeState(eT, -1)) AC3_RETURN_FALSE; }
                        entered = true;
                    }
                    if (entered) {
                        if (edgeStates[oppB] == -1) { if (!setEdgeState(oppR, 1)) AC3_RETURN_FALSE; }
                        else if (edgeStates[oppB] == 1) { if (!setEdgeState(oppR, -1)) AC3_RETURN_FALSE; }
                        if (edgeStates[oppR] == -1) { if (!setEdgeState(oppB, 1)) AC3_RETURN_FALSE; }
                        else if (edgeStates[oppR] == 1) { if (!setEdgeState(oppB, -1)) AC3_RETURN_FALSE; }
                    }
                }
                // Bottom-Left cell (cr=r, cc=c-1)
                if (getClue(r, c - 1) == 2) {
                    bool entered = (edgeStates[eR] == 1 && edgeStates[eT] == -1) || (edgeStates[eR] == -1 && edgeStates[eT] == 1);
                    bool entering_possible = (edgeStates[eR] == 1 && edgeStates[eT] == 0) || (edgeStates[eR] == 0 && edgeStates[eT] == 1);
                    int oppB = getHEdgeIndex(r + 1, c - 1);
                    int oppL = getVEdgeIndex(r, c - 1);
                    if (entering_possible && (edgeStates[oppB] == -1 || edgeStates[oppL] == -1)) {
                        if (edgeStates[eR] != 1) { if (!setEdgeState(eR, -1)) AC3_RETURN_FALSE; }
                        if (edgeStates[eT] != 1) { if (!setEdgeState(eT, -1)) AC3_RETURN_FALSE; }
                        entered = true;
                    }
                    if (entered) {
                        if (edgeStates[oppB] == -1) { if (!setEdgeState(oppL, 1)) AC3_RETURN_FALSE; }
                        else if (edgeStates[oppB] == 1) { if (!setEdgeState(oppL, -1)) AC3_RETURN_FALSE; }
                        if (edgeStates[oppL] == -1) { if (!setEdgeState(oppB, 1)) AC3_RETURN_FALSE; }
                        else if (edgeStates[oppL] == 1) { if (!setEdgeState(oppB, -1)) AC3_RETURN_FALSE; }
                    }
                }
                // Top-Right cell (cr=r-1, cc=c)
                if (getClue(r - 1, c) == 2) {
                    bool entered = (edgeStates[eL] == 1 && edgeStates[eB] == -1) || (edgeStates[eL] == -1 && edgeStates[eB] == 1);
                    bool entering_possible = (edgeStates[eL] == 1 && edgeStates[eB] == 0) || (edgeStates[eL] == 0 && edgeStates[eB] == 1);
                    int oppT = getHEdgeIndex(r - 1, c);
                    int oppR = getVEdgeIndex(r - 1, c + 1);
                    if (entering_possible && (edgeStates[oppT] == -1 || edgeStates[oppR] == -1)) {
                        if (edgeStates[eL] != 1) { if (!setEdgeState(eL, -1)) AC3_RETURN_FALSE; }
                        if (edgeStates[eB] != 1) { if (!setEdgeState(eB, -1)) AC3_RETURN_FALSE; }
                        entered = true;
                    }
                    if (entered) {
                        if (edgeStates[oppT] == -1) { if (!setEdgeState(oppR, 1)) AC3_RETURN_FALSE; }
                        else if (edgeStates[oppT] == 1) { if (!setEdgeState(oppR, -1)) AC3_RETURN_FALSE; }
                        if (edgeStates[oppR] == -1) { if (!setEdgeState(oppT, 1)) AC3_RETURN_FALSE; }
                        else if (edgeStates[oppR] == 1) { if (!setEdgeState(oppT, -1)) AC3_RETURN_FALSE; }
                    }
                }
                // Top-Left cell (cr=r-1, cc=c-1)
                if (getClue(r - 1, c - 1) == 2) {
                    bool entered = (edgeStates[eR] == 1 && edgeStates[eB] == -1) || (edgeStates[eR] == -1 && edgeStates[eB] == 1);
                    bool entering_possible = (edgeStates[eR] == 1 && edgeStates[eB] == 0) || (edgeStates[eR] == 0 && edgeStates[eB] == 1);
                    int oppT = getHEdgeIndex(r - 1, c - 1);
                    int oppL = getVEdgeIndex(r - 1, c - 1);
                    if (entering_possible && (edgeStates[oppT] == -1 || edgeStates[oppL] == -1)) {
                        if (edgeStates[eR] != 1) { if (!setEdgeState(eR, -1)) AC3_RETURN_FALSE; }
                        if (edgeStates[eB] != 1) { if (!setEdgeState(eB, -1)) AC3_RETURN_FALSE; }
                        entered = true;
                    }
                    if (entered) {
                        if (edgeStates[oppT] == -1) { if (!setEdgeState(oppL, 1)) AC3_RETURN_FALSE; }
                        else if (edgeStates[oppT] == 1) { if (!setEdgeState(oppL, -1)) AC3_RETURN_FALSE; }
                        if (edgeStates[oppL] == -1) { if (!setEdgeState(oppT, 1)) AC3_RETURN_FALSE; }
                        else if (edgeStates[oppL] == 1) { if (!setEdgeState(oppT, -1)) AC3_RETURN_FALSE; }
                    }
                }
                }

                // 5. Generalized Rule: Line entering a 1 corner
                if (ac3_current_difficulty_limit >= DIFF_HARD) {
                    RECORD_AC3_TIME(135);
                    // Bottom-Right cell (cr=r, cc=c)
                if (getClue(r, c) == 1) {
                    bool entered = (edgeStates[eL] == 1 && edgeStates[eT] == -1) || (edgeStates[eL] == -1 && edgeStates[eT] == 1);
                    if (entered) {
                        if (!setEdgeState(getHEdgeIndex(r + 1, c), -1)) AC3_RETURN_FALSE;
                        if (!setEdgeState(getVEdgeIndex(r, c + 1), -1)) AC3_RETURN_FALSE;
                    }
                }
                // Bottom-Left cell (cr=r, cc=c-1)
                if (getClue(r, c - 1) == 1) {
                    bool entered = (edgeStates[eR] == 1 && edgeStates[eT] == -1) || (edgeStates[eR] == -1 && edgeStates[eT] == 1);
                    if (entered) {
                        if (!setEdgeState(getHEdgeIndex(r + 1, c - 1), -1)) AC3_RETURN_FALSE;
                        if (!setEdgeState(getVEdgeIndex(r, c - 1), -1)) AC3_RETURN_FALSE;
                    }
                }
                // Top-Right cell (cr=r-1, cc=c)
                if (getClue(r - 1, c) == 1) {
                    bool entered = (edgeStates[eL] == 1 && edgeStates[eB] == -1) || (edgeStates[eL] == -1 && edgeStates[eB] == 1);
                    if (entered) {
                        if (!setEdgeState(getHEdgeIndex(r - 1, c), -1)) AC3_RETURN_FALSE;
                        if (!setEdgeState(getVEdgeIndex(r - 1, c + 1), -1)) AC3_RETURN_FALSE;
                    }
                }
                if (getClue(r - 1, c - 1) == 1) {
                    bool entered = (edgeStates[eR] == 1 && edgeStates[eB] == -1) || (edgeStates[eR] == -1 && edgeStates[eB] == 1);
                    if (entered) {
                        if (!setEdgeState(getHEdgeIndex(r - 1, c - 1), -1)) AC3_RETURN_FALSE;
                        if (!setEdgeState(getVEdgeIndex(r - 1, c - 1), -1)) AC3_RETURN_FALSE;
                    }
                }
                }
            }
            
            // 3. Process GF(2) (Flush if disabled)
            if (!enableGF2) {
                gf2_queue_head = gf2_queue_tail; // Flush
            }
        }
        
        if (restrictLogicToLocal) {
            gf2_queue_head = gf2_queue_tail; // Flush the GF2 queue
            if (cellStackTop == 0 && dotStackTop == 0) {
                break;
            }
            continue;
        }

        // Queues are empty. Check Jordan Curve Parity, Corner 2 rules, and 2-cell corner parity!
        if (ac3_current_difficulty_limit >= DIFF_GLOBAL_1) {
            RECORD_AC3_TIME(142);
            if (!deductJordanCurveParity()) AC3_RETURN_FALSE;
            
            RECORD_AC3_TIME(144);
            if (!applyInsideOutsideColoring()) AC3_RETURN_FALSE;
        }
        
        if (ac3_current_difficulty_limit >= DIFF_MEDIUM) {
            RECORD_AC3_TIME(143);
            if (!applyVirtualPathLogic()) AC3_RETURN_FALSE;
        }

        if (ac3_current_difficulty_limit >= DIFF_HARD) {
            RECORD_AC3_TIME(133);
            if (!applyAdvanced2Rules()) AC3_RETURN_FALSE;
            
            RECORD_AC3_TIME(132);
            for (int r = 0; r < rows; r++) {
                for (int c = 0; c < cols; c++) {
                    if (clues[r * cols + c] == 2) {
                        int tl_v = getVEdgeIndex(r - 1, c);
                        int tl_h = getHEdgeIndex(r, c - 1);
                        int br_v = getVEdgeIndex(r + 1, c + 1);
                        int br_h = getHEdgeIndex(r + 1, c + 1);
                        if (!deductParityPair(tl_v, tl_h, br_v, br_h)) AC3_RETURN_FALSE;
                        
                        int tr_v = getVEdgeIndex(r - 1, c + 1);
                        int tr_h = getHEdgeIndex(r, c + 1);
                        int bl_v = getVEdgeIndex(r + 1, c);
                        int bl_h = getHEdgeIndex(r + 1, c - 1);
                        if (!deductParityPair(tr_v, tr_h, bl_v, bl_h)) AC3_RETURN_FALSE;
                    }
                }
            }
        }
        
        bool cycleChanged = false;
        if (ac3_current_difficulty_limit >= DIFF_GLOBAL_2) {
            RECORD_AC3_TIME(141);
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
                        if (!setEdgeState(i, -1)) AC3_RETURN_FALSE;
                        if (edgeStates[i] == -1) cycleChanged = true;
                    }
                }
            }
        }
        }
        
        if (cellStackTop == 0 && dotStackTop == 0 && !cycleChanged) {
            // Only when absolutely everything is exhausted, run the O(V+E) Bridge Detection
            if (enableAdvancedAC3) {
                if (ac3_current_difficulty_limit >= DIFF_GLOBAL_3) { RECORD_AC3_TIME(152); if (!runUniversalParityCheck()) AC3_RETURN_FALSE; }
            }
            
            if (ac3_current_difficulty_limit >= DIFF_EXTREME && enable_deduction_logging && !restrictLogicToLocal) {
                int edges_before = 0;
                for(int i=0; i<numEdges; i++) if (edgeStates[i] != 0) edges_before++;
                
                RECORD_AC3_TIME(161);
                if (!applyLUT()) AC3_RETURN_FALSE;
                RECORD_AC3_TIME(161);
                if (!applyBoundaryLUTs()) AC3_RETURN_FALSE;
                
                int edges_after = 0;
                for(int i=0; i<numEdges; i++) if (edgeStates[i] != 0) edges_after++;
                
                if (edges_after > edges_before) {
                    for(int r=0; r<rows; r++) {
                        for(int c=0; c<cols; c++) cellStack[cellStackTop++] = r * cols + c;
                    }
                    for(int r=0; r<=rows; r++) {
                        for(int c=0; c<=cols; c++) dotStack[dotStackTop++] = r * (cols + 1) + c;
                    }
                    continue;
                }
            }
            
            if (cellStackTop == 0 && dotStackTop == 0) {
                if (enableGF2 && !isDoingLookahead && gf2_queue_head < gf2_queue_tail) {
                    if (ac3_current_difficulty_limit >= DIFF_GLOBAL_4) { 
                        RECORD_AC3_TIME(151); 
                        if (!batchUpdateGlobalGF2()) AC3_RETURN_FALSE; 
                        continue; 
                    }
                    break; // Blocked by difficulty, stop inferring
                }
                if (!enableGF2 || isDoingLookahead || gf2_queue_head == gf2_queue_tail) {
                    break;
                }
            }
        }
    }
    AC3_RETURN_TRUE;
}

static inline bool deductIncremental() {
    double t0 = emscripten_get_now();
    bool res = deductIncremental_internal();
    perf_ac3 += emscripten_get_now() - t0;
    return res;
}

EMSCRIPTEN_KEEPALIVE
bool deduct() {
    deduction_history_count = 0;
    dsuInitFromCurrent();
    clearStacks();
    
    if (!applyStaticRules()) {
        return false;
    }
    
    // Push all cells and dots to stacks so that deductIncremental evaluates the entire board.
    // This is necessary because JS writes directly to edgeStates without calling setEdgeState,
    // and applyStaticRules() clears the stacks.
    for (int r = 0; r <= rows; r++) {
        for (int c = 0; c <= cols; c++) {
            pushDot(r, c);
        }
    }
    for (int r = 0; r < rows; r++) {
        for (int c = 0; c < cols; c++) {
            pushCell(r, c);
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
        // Motivated by clue 2 or 3
        if (r > 0 && clues[(r - 1) * cols + c] >= 2) return true;
        if (r < rows && clues[r * cols + c] >= 2) return true;
        dotA = r * (cols + 1) + c;
        dotB = dotA + 1;
    } else {
        int vIdx = e - numH;
        r = vIdx / (cols + 1);
        c = vIdx % (cols + 1);
        // Motivated by clue 2 or 3
        if (c > 0 && clues[r * cols + (c - 1)] >= 2) return true;
        if (c < cols && clues[r * cols + c] >= 2) return true;
        dotA = r * (cols + 1) + c;
        dotB = dotA + (cols + 1);
    }
    
    // Motivated by extending an existing line (1)
    int edges[4];
    int count = getDotEdges(dotA / (cols + 1), dotA % (cols + 1), edges);
    for (int i = 0; i < count; i++) {
        if (edges[i] != e && edgeStates[edges[i]] == 1) return true;
    }
    
    count = getDotEdges(dotB / (cols + 1), dotB % (cols + 1), edges);
    for (int i = 0; i < count; i++) {
        if (edges[i] != e && edgeStates[edges[i]] == 1) return true;
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
        return -10; // Contradiction
    }
    
    while (true) {
        bool progressInPhase = false;
        
        if (enable_deduction_logging) {
            ac3_current_difficulty_limit = 1;
            while (ac3_current_difficulty_limit <= DIFF_LOOKAHEAD) {
                int edges_before = 0;
                for(int i=0; i<numEdges; i++) if (edgeStates[i] != 0) edges_before++;
                
                if (!deductIncremental()) {
                    return -11;
                }
                
                int edges_after = 0;
                for(int i=0; i<numEdges; i++) if (edgeStates[i] != 0) edges_after++;
                
                if (edges_after > edges_before) {
                    ac3_current_difficulty_limit = 1;
                    progressInPhase = true;
                } else {
                    ac3_current_difficulty_limit++;
                }
                
                bool allDecided = true;
                for (int i = 0; i < numEdges; i++) {
                    if (edgeStates[i] == 0) { allDecided = false; break; }
                }
                if (allDecided) return isSolved() ? 1 : 0;
            }
        } else {
            ac3_current_difficulty_limit = DIFF_LOOKAHEAD;
            int edges_before = 0;
            for(int i=0; i<numEdges; i++) if (edgeStates[i] != 0) edges_before++;
            if (!deductIncremental()) return 0;
            int edges_after = 0;
            for(int i=0; i<numEdges; i++) if (edgeStates[i] != 0) edges_after++;
            if (edges_after > edges_before) progressInPhase = true;
            
            bool allDecided = true;
            for (int i = 0; i < numEdges; i++) {
                if (edgeStates[i] == 0) { allDecided = false; break; }
            }
            if (allDecided) return isSolved() ? 1 : 0;
        }
        
        // In deduction logging mode, run 1-step lookahead as Level 10 logic.
        bool lookaheadFound = false;
        double t_lookahead_start = emscripten_get_now();
        
                
        for (int i = 0; i < numEdges; i++) {
            if (edgeStates[i] == 0) {
                if (!isEdgeConstrained(i)) continue; // Prune unconstrained edges
                
                // Scenario A: Assume Line (1)
                int checkpoint = dsuHistoryCount;
                int8_t backupEdges[MAX_EDGES];
                memcpy(backupEdges, edgeStates, numEdges);
                
                lookaheadConfirmedCount = 0;
                isDoingLookahead = true;
                lookaheadEdgeTests++;
                
                int oldLimit = lookaheadMaxLimit;
                lookaheadMaxLimit = 0; 
                bool lineSuccess = setEdgeState(i, 1) && deductIncremental();
                int8_t lineEdges[MAX_EDGES];
                if (lineSuccess) {
                    memcpy(lineEdges, edgeStates, numEdges);
                }
                lookaheadMaxLimit = oldLimit;
                isDoingLookahead = false;
                
                dsuRollback(checkpoint);
                memcpy(edgeStates, backupEdges, numEdges);
                gf2_queue_head = 0; gf2_queue_tail = 0;
                clearStacks();
                
                if (!lineSuccess) {
                    extern int lookaheadForcedEdgesTotal;
                    lookaheadForcedEdgesTotal++;
                    
                    RECORD_AC3_TIME(200);
                    if (!setEdgeState(i, -1)) return 0;
                    
                    lookaheadFound = true;
                    for(int r=0; r<rows; r++) for(int c=0; c<cols; c++) cellStack[cellStackTop++] = r*cols+c;
                    for(int r=0; r<=rows; r++) for(int c=0; c<=cols; c++) dotStack[dotStackTop++] = r*(cols+1)+c;
                    break;
                }
                
                // Scenario B: Assume Cross (-1)
                checkpoint = dsuHistoryCount;
                memcpy(backupEdges, edgeStates, numEdges);
                
                lookaheadConfirmedCount = 0;
                isDoingLookahead = true;
                lookaheadEdgeTests++;
                
                oldLimit = lookaheadMaxLimit;
                lookaheadMaxLimit = 0;
                bool crossSuccess = setEdgeState(i, -1) && deductIncremental();
                
                bool forcedFound = false;
                int forcedEdges[MAX_EDGES];
                int8_t forcedStates[MAX_EDGES];
                int forcedCount = 0;
                
                if (crossSuccess) {
                    for (int j = 0; j < numEdges; j++) {
                        if (backupEdges[j] == 0 && lineEdges[j] != 0 && lineEdges[j] == edgeStates[j]) {
                            forcedEdges[forcedCount] = j;
                            forcedStates[forcedCount] = lineEdges[j];
                            forcedCount++;
                        }
                    }
                }
                
                lookaheadMaxLimit = oldLimit;
                isDoingLookahead = false;
                
                dsuRollback(checkpoint);
                memcpy(edgeStates, backupEdges, numEdges);
                gf2_queue_head = 0; gf2_queue_tail = 0;
                clearStacks();
                
                if (!crossSuccess) {
                    extern int lookaheadForcedEdgesTotal;
                    lookaheadForcedEdgesTotal++;
                    
                    RECORD_AC3_TIME(200);
                    if (!setEdgeState(i, 1)) return 0;
                    
                    lookaheadFound = true;
                    for(int r=0; r<rows; r++) for(int c=0; c<cols; c++) cellStack[cellStackTop++] = r*cols+c;
                    for(int r=0; r<=rows; r++) for(int c=0; c<=cols; c++) dotStack[dotStackTop++] = r*(cols+1)+c;
                    break;
                } else if (forcedCount > 0) {
                    extern int lookaheadForcedEdgesTotal;
                    lookaheadForcedEdgesTotal += forcedCount;
                    
                    RECORD_AC3_TIME(201);
                    for (int k = 0; k < forcedCount; k++) {
                        if (!setEdgeState(forcedEdges[k], forcedStates[k])) return 0;
                    }
                    lookaheadFound = true;
                    for(int r=0; r<rows; r++) for(int c=0; c<cols; c++) cellStack[cellStackTop++] = r*cols+c;
                    for(int r=0; r<=rows; r++) for(int c=0; c<=cols; c++) dotStack[dotStackTop++] = r*(cols+1)+c;
                    break;
                }
            }
        }
        perf_lookahead += emscripten_get_now() - t_lookahead_start;
        
        bool allDecided = true;
        for (int i = 0; i < numEdges; i++) {
            if (edgeStates[i] == 0) { allDecided = false; break; }
        }
        if (allDecided) return isSolved() ? 1 : 0;
        
        if (!lookaheadFound) {
            return -2; // Stalled: even Lookahead could not find anything
        }
    }
}

EMSCRIPTEN_KEEPALIVE
int apply_lookahead_once() {
    // 1. Run full deduct() to populate DSU, stacks, and propagate current edgeStates.
    if (!deduct()) return -1;

    int found = 0;
    int constrained_count = 0;
    for (int i = 0; i < numEdges; i++) {
        if (edgeStates[i] == 0) {
            if (!isEdgeConstrained(i)) continue;
            constrained_count++;
            
            // Assume Line (1)
            int checkpoint = dsuHistoryCount;
            int8_t backupEdges[MAX_EDGES];
            memcpy(backupEdges, edgeStates, numEdges);
            
            isDoingLookahead = true;
            int oldLimit = lookaheadMaxLimit;
            lookaheadMaxLimit = 0;
            bool lineSuccess = setEdgeState(i, 1) && deductIncremental();
            lookaheadMaxLimit = oldLimit;
            isDoingLookahead = false;
            
            dsuRollback(checkpoint);
            memcpy(edgeStates, backupEdges, numEdges);
            gf2_queue_head = 0; gf2_queue_tail = 0;
            clearStacks();
            
            if (!lineSuccess) {
                deduction_history_count = 0;
                RECORD_AC3_TIME(200); // Lookahead (Contradiction on Line)
                if (!setEdgeState(i, -1)) return -1;
                if (!deductIncremental()) return -1;
                found++;
                continue; // Move to next edge
            }
            
            // Assume Cross (-1)
            checkpoint = dsuHistoryCount;
            memcpy(backupEdges, edgeStates, numEdges);
            
            isDoingLookahead = true;
            oldLimit = lookaheadMaxLimit;
            lookaheadMaxLimit = 0;
            bool crossSuccess = setEdgeState(i, -1) && deductIncremental();
            lookaheadMaxLimit = oldLimit;
            isDoingLookahead = false;
            
            dsuRollback(checkpoint);
            memcpy(edgeStates, backupEdges, numEdges);
            gf2_queue_head = 0; gf2_queue_tail = 0;
            clearStacks();
            
            if (!crossSuccess) {
                deduction_history_count = 0;
                RECORD_AC3_TIME(200); // Lookahead (Contradiction on Cross)
                if (!setEdgeState(i, 1)) return -1;
                if (!deductIncremental()) return -1;
                found++;
            }
        }
    }
    
    printf("[WASM Lookahead] Checked %d constrained edges. Found %d forced edges.\n", constrained_count, found);
    return found;
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

// Slitherlink Aesthetic Rule: Eliminate adjacent '0' clues
static void eliminateAdjacentZerosSymmetrically() {
    bool changed;
    do {
        changed = false;
        int candidates[MAX_CELLS];
        int candidateCount = 0;

        for (int r = 0; r < rows; r++) {
            for (int c = 0; c < cols; c++) {
                if (clues[r * cols + c] != 0) continue;
                bool hasAdj0 = false;
                for (int dr = -1; dr <= 1; dr++) {
                    for (int dc = -1; dc <= 1; dc++) {
                        if (dr == 0 && dc == 0) continue;
                        int nr = r + dr;
                        int nc = c + dc;
                        if (nr >= 0 && nr < rows && nc >= 0 && nc < cols) {
                            if (clues[nr * cols + nc] == 0) {
                                hasAdj0 = true;
                                break;
                            }
                        }
                    }
                    if (hasAdj0) break;
                }
                if (hasAdj0) {
                    candidates[candidateCount++] = r * cols + c;
                }
            }
        }

        if (candidateCount > 0) {
            int pickIdx = candidates[rand() % candidateCount];
            int pickR = pickIdx / cols;
            int pickC = pickIdx % cols;
            int symR = rows - 1 - pickR;
            int symC = cols - 1 - pickC;
            
            clues[pickR * cols + pickC] = -1;
            clues[symR * cols + symC] = -1;
            changed = true;
        }
    } while (changed);
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
    set_solver_difficulty(difficulty);

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
        // Human solvability check
        set_solver_difficulty(difficulty);
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

// 判定用関数：Epic Criteria（高度なアルゴリズムが使われたか）
static bool checkEpicCriteria(const char* difficulty) {
    static int8_t backupEdges[MAX_EDGES];
    memcpy(backupEdges, edgeStates, numEdges);
    memset(edgeStates, 0, numEdges);

    reset_ac3_rule_times();
    
    // Check solvability with the specific difficulty setting
    bool solvable = checkSolvability(difficulty);
    
    bool usedGF2 = (ac3_rule_hit_counts[151] > 0); // 151: GF2
    bool usedJordan = (ac3_rule_hit_counts[142] > 0); // 142: Jordan Curve
    bool usedNoEarlyClose = (ac3_rule_hit_counts[141] > 0); // 141: ループの早期閉路禁止
    bool usedBridge = (ac3_rule_hit_counts[152] > 0); // 152: 全体連結性(Bridge)
    
    // 全ての高度な大域定理が「新しいエッジを確定させた」場合にのみOKとする（真の全部乗せ）
    bool meetsCriteria = (usedGF2 && usedJordan && usedNoEarlyClose && usedBridge);
    
    memcpy(edgeStates, backupEdges, numEdges);
    return meetsCriteria && solvable;
}

// FULL MINIMIZATION ENGINE IN C (TOP-DOWN & SYMMETRIC)
static void generate_puzzle_wasm_internal(const char* difficulty) {
    debugTimeoutCount = 0;
    debugContradictionCount = 0;
    lookaheadEdgeTests = 0;
    lookaheadForcedEdgesTotal = 0;
    staticRuleEdgesTotal = 0;
    lutEdgesTotal = 0;
    
    printf("[C Debug] Starting generate_puzzle_wasm. diff=%s, rows=%d, cols=%d\n", difficulty, rows, cols);
    set_solver_difficulty(difficulty);

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
        eliminateAdjacentZerosSymmetrically();
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

        bool batchSolvable = checkSolvability(difficulty);

        if (batchSolvable) {
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

    // Pass 3: Asymmetric Single Clue Removal for Master ONLY
    if (strcmp(difficulty, "Master") == 0 || strcmp(difficulty, "master") == 0) {
        printf("[C Generator] Starting Asymmetric Single Clue Removal for %s...\n", difficulty);
        
        int singleClues[MAX_CELLS];
        int singleCount = 0;
        for (int idx = 0; idx < totalCells; idx++) {
            if (clues[idx] != -1) {
                singleClues[singleCount++] = idx;
            }
        }
        
        // Shuffle single clues
        for (int idx = singleCount - 1; idx > 0; idx--) {
            int jdx = rand() % (idx + 1);
            int temp = singleClues[idx];
            singleClues[idx] = singleClues[jdx];
            singleClues[jdx] = temp;
        }
        
        for (int idx = 0; idx < singleCount; idx++) {
            int cell = singleClues[idx];
            int8_t savedClue = clues[cell];
            if (savedClue == -1) continue;
            
            clues[cell] = -1;
            
            bool singleSolvable = checkSolvability(difficulty);
            
            if (singleSolvable) {
                currentClueCount--;
                printf("[C Generator] Asymmetric removal successful! Clues remaining: %d\n", currentClueCount);
            } else {
                clues[cell] = savedClue; // Rollback
            }
        }
        printf("[C Generator] Finished asymmetric minimization! Final clues remaining: %d/%d\n", currentClueCount, totalCells);
    }

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
void generate_puzzle_wasm(const char* difficulty) {
    generate_puzzle_wasm_internal(difficulty);
}

EMSCRIPTEN_KEEPALIVE
void set_advanced_ac3(bool enable) {
    enableAdvancedAC3 = enable;
}

EMSCRIPTEN_KEEPALIVE
int get_lookahead_count() {
    return lookaheadEdgeTests;
}

// --- Deduction Logging API ---
EMSCRIPTEN_KEEPALIVE
int get_deduction_log_count() {
    return deduction_log_count;
}

EMSCRIPTEN_KEEPALIVE
DeductionLog* get_deduction_logs_ptr() {
    return deduction_logs;
}

EMSCRIPTEN_KEEPALIVE
int analyze_puzzle(const char* difficulty) {
    memset(edgeStates, 0, numEdges);
    deduction_log_count = 0;
    enable_deduction_logging = true;
    
    int result = check_human_solvability();
    
    enable_deduction_logging = false;
    ac3_current_difficulty_limit = DIFF_LOOKAHEAD;
    return result;
}

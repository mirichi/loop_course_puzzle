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

// Generator variables
static int8_t genCells[MAX_ROWS][MAX_COLS];

// pre-allocated stack for backtracking search to avoid constant allocations
#define MAX_BACKTRACK_DEPTH 200
static int8_t backupStack[MAX_BACKTRACK_DEPTH][MAX_EDGES];

// Graph adjacency list arrays for loop connection tracing (avoids allocations)
static int adj[MAX_DOTS][4];
static int adjCount[MAX_DOTS];
static bool visitedDots[MAX_DOTS];

// BFS cell queue arrays
static int queueR[MAX_CELLS];
static int queueC[MAX_CELLS];
static bool visitedCells[MAX_ROWS][MAX_COLS];

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

        if (hasUndecided) {
            // Verify if all clues are fully satisfied
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
                    if (lines != clue) {
                        return false; // Loop closed early while unsatisfied clues remain
                    }
                }
            }

            // Clues satisfied, fill remaining undecided as crosses
            for (int i = 0; i < numEdges; i++) {
                if (edgeStates[i] == 0) {
                    edgeStates[i] = -1;
                }
            }
        }
    }

    return true;
}

// LOGICAL DEDUCTION ENGINE
EMSCRIPTEN_KEEPALIVE
bool deduct() {
    bool changed = true;
    while (changed) {
        changed = false;

        // 1. Cell clues deductions
        for (int r = 0; r < rows; r++) {
            for (int c = 0; c < cols; c++) {
                int clue = clues[r * cols + c];
                if (clue == -1) continue;

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
                            edgeStates[undecided[j]] = -1;
                            changed = true;
                        }
                    } else if (crosses == (4 - clue)) {
                        for (int j = 0; j < undecidedCount; j++) {
                            edgeStates[undecided[j]] = 1;
                            changed = true;
                        }
                    }
                }
            }
        }

        // 2. Dot degree deductions
        for (int r = 0; r <= rows; r++) {
            for (int c = 0; c <= cols; c++) {
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
                    return false; // Degree limit exceeded
                }

                if (undecidedCount > 0) {
                    if (lines == 2) {
                        for (int j = 0; j < undecidedCount; j++) {
                            edgeStates[undecided[j]] = -1;
                            changed = true;
                        }
                    } else if (lines == 1 && undecidedCount == 1) {
                        edgeStates[undecided[0]] = 1;
                        changed = true;
                    } else if (lines == 0 && undecidedCount == 1) {
                        edgeStates[undecided[0]] = -1;
                        changed = true;
                    }
                } else {
                    if (lines != 0 && lines != 2) {
                        return false; // Degree violation (degree must be 0 or 2)
                    }
                }
            }
        }
    }

    if (!preventsPrematureLoops()) {
        return false;
    }

    return true;
}

// SOLVED STATE VERIFICATION
EMSCRIPTEN_KEEPALIVE
bool isSolved() {
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

    memcpy(backupStack[depth], edgeStates, numEdges);

    if (!deduct()) {
        memcpy(edgeStates, backupStack[depth], numEdges);
        return;
    }

    if (isSolved()) {
        if (foundSolutionsCount < MAX_SOLUTIONS) {
            memcpy(foundSolutions[foundSolutionsCount++], edgeStates, numEdges);
        }
        memcpy(edgeStates, backupStack[depth], numEdges);
        return;
    }

    int undecidedIdx = -1;
    for (int i = 0; i < numEdges; i++) {
        if (edgeStates[i] == 0) {
            undecidedIdx = i;
            break;
        }
    }

    if (undecidedIdx == -1) {
        memcpy(edgeStates, backupStack[depth], numEdges);
        return;
    }

    if (foundSolutionsCount >= 2 || (findSingle && foundSolutionsCount >= 1)) {
        memcpy(edgeStates, backupStack[depth], numEdges);
        return;
    }

    int branchIdx = undecidedIdx;
    bool foundBranch = false;

    for (int r = 0; r < rows; r++) {
        for (int c = 0; c < cols; c++) {
            if (clues[r * cols + c] != -1) {
                int cellEdges[4];
                getCellEdges(r, c, cellEdges);
                for (int j = 0; j < 4; j++) {
                    int idx = cellEdges[j];
                    if (edgeStates[idx] == 0) {
                        branchIdx = idx;
                        foundBranch = true;
                        break;
                    }
                }
            }
            if (foundBranch) break;
        }
        if (foundBranch) break;
    }

    edgeStates[branchIdx] = 1;
    backtrack(depth + 1, findSingle, maxSteps);

    if (foundSolutionsCount >= 2 || (findSingle && foundSolutionsCount >= 1) || isTimeout) {
        memcpy(edgeStates, backupStack[depth], numEdges);
        return;
    }

    edgeStates[branchIdx] = -1;
    backtrack(depth + 1, findSingle, maxSteps);

    memcpy(edgeStates, backupStack[depth], numEdges);
}

EMSCRIPTEN_KEEPALIVE
int solve_puzzle_wasm(bool findSingle, int maxSteps) {
    foundSolutionsCount = 0;
    explorationSteps = 0;
    isTimeout = false;
    memset(foundSolutions, 0, sizeof(foundSolutions));

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

                        if (insideNeighbors > 0 && insideNeighbors < 4 && !wouldForm4x4Inside) {
                            double neighborScore = (insideNeighbors == 1) ? 35.0 : ((insideNeighbors == 2) ? 5.0 : 1.0);
                            double dist = pow(r - avgR, 2) + pow(c - avgC, 2);
                            double distScore = 1.0 + dist * 0.15;

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
                                    if (isCollinear) bendMultiplier = 0.3; // Straight penalty
                                    else bendMultiplier = 2.0;            // Curved turn bonus
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
        if (insideCount >= minAcceptableInsideCount && checkSectorCoverage(genCells, numSectorsX, numSectorsY)) {
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

// Fast solver validation for minimization
static bool checkSolvability(const char* difficulty) {
    int maxSteps = strcmp(difficulty, "easy") == 0 ? 0 : 50;
    int totalCells = rows * cols;
    if (totalCells > 150) {
        maxSteps = strcmp(difficulty, "easy") == 0 ? 0 : (strcmp(difficulty, "medium") == 0 ? 2 : 8);
    }

    // Backup current edgeStates before solving
    static int8_t origEdges[MAX_EDGES];
    memcpy(origEdges, edgeStates, numEdges);

    if (maxSteps == 0) {
        // Pure deduction solver check
        memset(edgeStates, 0, numEdges);
        bool success = deduct() && isSolved();
        memcpy(edgeStates, origEdges, numEdges); // restore original
        return success;
    }

    // Backtrack solver check
    memset(edgeStates, 0, numEdges);
    int solutions = solve_puzzle_wasm(false, maxSteps);
    memcpy(edgeStates, origEdges, numEdges); // restore original

    return solutions == 1;
}

// FULL MINIMIZATION ENGINE IN C
EMSCRIPTEN_KEEPALIVE
void generate_puzzle_wasm(const char* difficulty) {
    generateRandomLoop();
    calculateClues();

    // Prepare coordinate lists
    static int cellR[MAX_CELLS];
    static int cellC[MAX_CELLS];
    int cellCount = 0;
    for (int r = 0; r < rows; r++) {
        for (int c = 0; c < cols; c++) {
            cellR[cellCount] = r;
            cellC[cellCount] = c;
            cellCount++;
        }
    }

    // Shuffle coords
    for (int i = cellCount - 1; i > 0; i--) {
        int j = rand() % (i + 1);
        int tempR = cellR[i];
        int tempC = cellC[i];
        cellR[i] = cellR[j];
        cellC[i] = cellC[j];
        cellR[j] = tempR;
        cellC[j] = tempC;
    }

    // Sort coordinates by clue priority: hide 0s first, keep 3s last
    for (int i = 0; i < cellCount - 1; i++) {
        for (int j = i + 1; j < cellCount; j++) {
            int clueI = clues[cellR[i] * cols + cellC[i]];
            int clueJ = clues[cellR[j] * cols + cellC[j]];
            int prioI = (clueI == 0) ? 0 : ((clueI == 3) ? 2 : 1);
            int prioJ = (clueJ == 0) ? 0 : ((clueJ == 3) ? 2 : 1);

            if (prioI > prioJ) {
                int tempR = cellR[i];
                int tempC = cellC[i];
                cellR[i] = cellR[j];
                cellC[i] = cellC[j];
                cellR[j] = tempR;
                cellC[j] = tempC;
            }
        }
    }

    double keepRatio = 0.45;
    if (strcmp(difficulty, "medium") == 0) keepRatio = 0.32;
    else if (strcmp(difficulty, "hard") == 0) keepRatio = 0.22;

    int targetKeepCount = (int)(rows * cols * keepRatio);
    int currentClueCount = rows * cols;
    bool isLargeBoard = (rows * cols > 150);

    // PASS 1: LARGE CHUNKS (size 20 or 8)
    int chunkSize1 = isLargeBoard ? 20 : (rows * cols > 60 ? 8 : 1);
    if (chunkSize1 > 1) {
        for (int i = 0; i < cellCount; i += chunkSize1) {
            if (currentClueCount <= targetKeepCount) break;

            int chunkR[20];
            int chunkC[20];
            int chunkOrigVals[20];
            int chunkLength = 0;

            for (int j = 0; j < chunkSize1 && (i + j) < cellCount; j++) {
                int r = cellR[i + j];
                int c = cellC[i + j];
                int val = clues[r * cols + c];
                if (val != -1) {
                    if (strcmp(difficulty, "easy") == 0 && val == 3 && ((double)rand() / RAND_MAX) < 0.8) {
                        continue;
                    }
                    chunkR[chunkLength] = r;
                    chunkC[chunkLength] = c;
                    chunkOrigVals[chunkLength] = val;
                    chunkLength++;
                }
            }

            if (chunkLength == 0) continue;
            if (currentClueCount - chunkLength < targetKeepCount) continue;

            // Clear chunk clues
            for (int k = 0; k < chunkLength; k++) {
                clues[chunkR[k] * cols + chunkC[k]] = -1;
            }

            if (checkSolvability(difficulty)) {
                currentClueCount -= chunkLength;
            } else {
                // Restore chunk clues
                for (int k = 0; k < chunkLength; k++) {
                    clues[chunkR[k] * cols + chunkC[k]] = chunkOrigVals[k];
                }
            }
        }
    }

    // PASS 2: SMALL CHUNKS (size 5 or 3)
    int remainingCount = 0;
    static int remR[MAX_CELLS];
    static int remC[MAX_CELLS];
    for (int i = 0; i < cellCount; i++) {
        int r = cellR[i];
        int c = cellC[i];
        if (clues[r * cols + c] != -1) {
            remR[remainingCount] = r;
            remC[remainingCount] = c;
            remainingCount++;
        }
    }

    int chunkSize2 = isLargeBoard ? 5 : (rows * cols > 60 ? 3 : 2);
    for (int i = 0; i < remainingCount; i += chunkSize2) {
        if (currentClueCount <= targetKeepCount) break;

        int chunkR[5];
        int chunkC[5];
        int chunkOrigVals[5];
        int chunkLength = 0;

        for (int j = 0; j < chunkSize2 && (i + j) < remainingCount; j++) {
            int r = remR[i + j];
            int c = remC[i + j];
            int val = clues[r * cols + c];
            if (val != -1) {
                if (strcmp(difficulty, "easy") == 0 && val == 3 && ((double)rand() / RAND_MAX) < 0.8) {
                    continue;
                }
                chunkR[chunkLength] = r;
                chunkC[chunkLength] = c;
                chunkOrigVals[chunkLength] = val;
                chunkLength++;
            }
        }

        if (chunkLength == 0) continue;
        if (currentClueCount - chunkLength < targetKeepCount) continue;

        // Clear chunk clues
        for (int k = 0; k < chunkLength; k++) {
            clues[chunkR[k] * cols + chunkC[k]] = -1;
        }

        if (checkSolvability(difficulty)) {
            currentClueCount -= chunkLength;
        } else {
            // Restore chunk clues
            for (int k = 0; k < chunkLength; k++) {
                clues[chunkR[k] * cols + chunkC[k]] = chunkOrigVals[k];
            }
        }
    }

    // PASS 3: INDIVIDUAL FINE TUNING (size 1)
    int finalRemainingCount = 0;
    static int finalRemR[MAX_CELLS];
    static int finalRemC[MAX_CELLS];
    for (int i = 0; i < cellCount; i++) {
        int r = cellR[i];
        int c = cellC[i];
        if (clues[r * cols + c] != -1) {
            finalRemR[finalRemainingCount] = r;
            finalRemC[finalRemainingCount] = c;
            finalRemainingCount++;
        }
    }

    for (int i = 0; i < finalRemainingCount; i++) {
        if (currentClueCount <= targetKeepCount) break;

        int r = finalRemR[i];
        int c = finalRemC[i];
        int val = clues[r * cols + c];

        if (strcmp(difficulty, "easy") == 0 && val == 3 && ((double)rand() / RAND_MAX) < 0.8) {
            continue;
        }

        clues[r * cols + c] = -1;
        currentClueCount--;

        if (checkSolvability(difficulty)) {
            // keep deleted
        } else {
            clues[r * cols + c] = val; // restore
            currentClueCount++;
        }
    }

    // Finalize: original solved loop remains in edgeStates
    memset(genCells, 0, sizeof(genCells));
}

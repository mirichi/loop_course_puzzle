#ifndef LUT_MODULE_H
#define LUT_MODULE_H

#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>

extern int rows;
extern int cols;
extern int8_t clues[];

// Function prototypes from loopcourse.c
int getHEdgeIndex(int r, int c);
int getVEdgeIndex(int r, int c);
bool setEdgeState(int edgeIdx, int8_t state);

#define NUM_PATTERNS 1953125
uint64_t* valid_mask_AND = NULL;
uint64_t* valid_mask_OR = NULL;

void init_lut() {
    if (valid_mask_AND != NULL) return;

    valid_mask_AND = (uint64_t*)malloc(NUM_PATTERNS * sizeof(uint64_t));
    valid_mask_OR = (uint64_t*)malloc(NUM_PATTERNS * sizeof(uint64_t));
    
    for (int i = 0; i < NUM_PATTERNS; i++) {
        valid_mask_AND[i] = 0xFFFFFFFFFFULL; // 40 bits of 1s
        valid_mask_OR[i] = 0;
    }

    int total = 1 << 24;
    int validEdgeConfigs = 0;
    uint64_t* validANDs = (uint64_t*)malloc(300000 * sizeof(uint64_t));
    uint64_t* validORs = (uint64_t*)malloc(300000 * sizeof(uint64_t));

    for (int i = 0; i < total; i++) {
        #define H_BIT(r, c) ((i >> ((r) * 3 + (c))) & 1)
        #define V_BIT(r, c) ((i >> (12 + (c) * 3 + (r))) & 1)
        
        bool invalid = false;
        for (int r = 0; r <= 3; r++) {
            for (int c = 0; c <= 3; c++) {
                int sum = 0;
                if (r > 0) sum += V_BIT(r - 1, c);
                if (r < 3) sum += V_BIT(r, c);
                if (c > 0) sum += H_BIT(r, c - 1);
                if (c < 3) sum += H_BIT(r, c);
                
                if ((r == 1 || r == 2) && (c == 1 || c == 2)) {
                    if (sum != 0 && sum != 2) { invalid = true; break; }
                } else {
                    if (sum > 2) { invalid = true; break; }
                }
            }
            if (invalid) break;
        }
        if (!invalid) {
            uint64_t base_state = i;
            
            // 1. Determine the 8 non-corner external edges
            // top non-corners
            if (V_BIT(0, 1) + H_BIT(0, 0) + H_BIT(0, 1) == 1) base_state |= (1ULL << (24 + 1));
            if (V_BIT(0, 2) + H_BIT(0, 1) + H_BIT(0, 2) == 1) base_state |= (1ULL << (24 + 2));
            // bottom non-corners
            if (V_BIT(2, 1) + H_BIT(3, 0) + H_BIT(3, 1) == 1) base_state |= (1ULL << (28 + 1));
            if (V_BIT(2, 2) + H_BIT(3, 1) + H_BIT(3, 2) == 1) base_state |= (1ULL << (28 + 2));
            // left non-corners
            if (H_BIT(1, 0) + V_BIT(0, 0) + V_BIT(1, 0) == 1) base_state |= (1ULL << (32 + 1));
            if (H_BIT(2, 0) + V_BIT(1, 0) + V_BIT(2, 0) == 1) base_state |= (1ULL << (32 + 2));
            // right non-corners
            if (H_BIT(1, 2) + V_BIT(0, 3) + V_BIT(1, 3) == 1) base_state |= (1ULL << (36 + 1));
            if (H_BIT(2, 2) + V_BIT(1, 3) + V_BIT(2, 3) == 1) base_state |= (1ULL << (36 + 2));

            // 2. Corner combinations
            int corner_sums[4];
            corner_sums[0] = V_BIT(0,0) + H_BIT(0,0);
            corner_sums[1] = V_BIT(0,3) + H_BIT(0,2);
            corner_sums[2] = V_BIT(2,0) + H_BIT(3,0);
            corner_sums[3] = V_BIT(2,3) + H_BIT(3,2);

            int pairs[3][2][2] = {
                {{0,0}, {1,1}}, // sum 0 -> ext sum 0 or 2
                {{0,1}, {1,0}}, // sum 1 -> ext sum 1
                {{0,0}, {0,0}}  // sum 2 -> ext sum 0
            };
            int num_pairs[3] = {2, 2, 1};
            
            int corner_bit1[4] = {24+0, 24+3, 28+0, 28+3}; // Top/Bottom edges
            int corner_bit2[4] = {32+0, 36+0, 32+3, 36+3}; // Left/Right edges

            uint64_t comp_AND = 0xFFFFFFFFFFFFFFFFULL;
            uint64_t comp_OR = 0;

            for(int i0=0; i0<num_pairs[corner_sums[0]]; i0++) {
                uint64_t s0 = base_state | ((uint64_t)pairs[corner_sums[0]][i0][0] << corner_bit1[0]) | ((uint64_t)pairs[corner_sums[0]][i0][1] << corner_bit2[0]);
                for(int i1=0; i1<num_pairs[corner_sums[1]]; i1++) {
                    uint64_t s1 = s0 | ((uint64_t)pairs[corner_sums[1]][i1][0] << corner_bit1[1]) | ((uint64_t)pairs[corner_sums[1]][i1][1] << corner_bit2[1]);
                    for(int i2=0; i2<num_pairs[corner_sums[2]]; i2++) {
                        uint64_t s2 = s1 | ((uint64_t)pairs[corner_sums[2]][i2][0] << corner_bit1[2]) | ((uint64_t)pairs[corner_sums[2]][i2][1] << corner_bit2[2]);
                        for(int i3=0; i3<num_pairs[corner_sums[3]]; i3++) {
                            uint64_t s3 = s2 | ((uint64_t)pairs[corner_sums[3]][i3][0] << corner_bit1[3]) | ((uint64_t)pairs[corner_sums[3]][i3][1] << corner_bit2[3]);
                            comp_AND &= s3;
                            comp_OR |= s3;
                        }
                    }
                }
            }
            validANDs[validEdgeConfigs] = comp_AND;
            validORs[validEdgeConfigs] = comp_OR;
            validEdgeConfigs++;
        }
    }

    int pow5[] = {1, 5, 25, 125, 625, 3125, 15625, 78125, 390625, 1953125};
    for (int eIdx = 0; eIdx < validEdgeConfigs; eIdx++) {
        uint64_t cAND = validANDs[eIdx];
        uint64_t cOR = validORs[eIdx];
        uint32_t i = cAND & 0xFFFFFF; // Extract internal 24 bits
        
        int clue_arr[9];
        for (int r = 0; r < 3; r++) {
            for (int c = 0; c < 3; c++) {
                clue_arr[r * 3 + c] = H_BIT(r, c) + H_BIT(r + 1, c) + V_BIT(r, c) + V_BIT(r, c + 1);
            }
        }
        
        for (int sub = 0; sub < 512; sub++) {
            int patternIdx = 0;
            for (int cell = 0; cell < 9; cell++) {
                if ((sub >> cell) & 1) {
                    patternIdx += 4 * pow5[cell];
                } else {
                    patternIdx += clue_arr[cell] * pow5[cell];
                }
            }
            valid_mask_AND[patternIdx] &= cAND;
            valid_mask_OR[patternIdx]  |= cOR;
        }
    }
    
    free(validANDs);
    free(validORs);
    #undef H_BIT
    #undef V_BIT
}

bool applyLUT() {
    if (valid_mask_AND == NULL) return true;
    
    int pow5[] = {1, 5, 25, 125, 625, 3125, 15625, 78125, 390625, 1953125};
    
    for (int r = -1; r < rows; r++) {
        for (int c = -1; c < cols; c++) {
            int patternIdx = 0;
            for (int dr = 0; dr < 3; dr++) {
                for (int dc = 0; dc < 3; dc++) {
                    int rr = r + dr;
                    int cc = c + dc;
                    int cellIdx = dr * 3 + dc;
                    if (rr >= 0 && rr < rows && cc >= 0 && cc < cols) {
                        int clue = clues[rr * cols + cc];
                        if (clue == -1) clue = 4;
                        patternIdx += clue * pow5[cellIdx];
                    } else {
                        patternIdx += 4 * pow5[cellIdx]; // Outside board = empty
                    }
                }
            }
            
            uint64_t fl = valid_mask_AND[patternIdx];
            uint64_t fc = valid_mask_OR[patternIdx];
            
            // Apply H edges
            for (int dr = 0; dr <= 3; dr++) {
                for (int dc = 0; dc < 3; dc++) {
                    int bit = dr * 3 + dc;
                    int rr = r + dr;
                    int cc = c + dc;
                    if (rr >= 0 && rr <= rows && cc >= 0 && cc < cols) {
                        int edgeIdx = getHEdgeIndex(rr, cc);
                        if ((fl >> bit) & 1) {
                            if (!setEdgeState(edgeIdx, 1)) return false;
                        }
                        if (!((fc >> bit) & 1)) {
                            if (!setEdgeState(edgeIdx, -1)) return false;
                        }
                    }
                }
            }
            
            // Apply V edges
            for (int dr = 0; dr < 3; dr++) {
                for (int dc = 0; dc <= 3; dc++) {
                    int bit = 12 + dc * 3 + dr;
                    int rr = r + dr;
                    int cc = c + dc;
                    if (rr >= 0 && rr < rows && cc >= 0 && cc <= cols) {
                        int edgeIdx = getVEdgeIndex(rr, cc);
                        if ((fl >> bit) & 1) {
                            if (!setEdgeState(edgeIdx, 1)) return false;
                        }
                        if (!((fc >> bit) & 1)) {
                            if (!setEdgeState(edgeIdx, -1)) return false;
                        }
                    }
                }
            }
            
            // Apply Top outer edges (r=-1, c=0..3 => V edges)
            for (int c_out = 0; c_out < 4; c_out++) {
                int bit = 24 + c_out;
                int rr = r - 1;
                int cc = c + c_out;
                if (rr >= 0 && rr < rows && cc >= 0 && cc <= cols) {
                    int edgeIdx = getVEdgeIndex(rr, cc);
                    if ((fl >> bit) & 1) { if (!setEdgeState(edgeIdx, 1)) return false; }
                    if (!((fc >> bit) & 1)) { if (!setEdgeState(edgeIdx, -1)) return false; }
                }
            }
            // Apply Bottom outer edges (r=3, c=0..3 => V edges)
            for (int c_out = 0; c_out < 4; c_out++) {
                int bit = 28 + c_out;
                int rr = r + 3;
                int cc = c + c_out;
                if (rr >= 0 && rr < rows && cc >= 0 && cc <= cols) {
                    int edgeIdx = getVEdgeIndex(rr, cc);
                    if ((fl >> bit) & 1) { if (!setEdgeState(edgeIdx, 1)) return false; }
                    if (!((fc >> bit) & 1)) { if (!setEdgeState(edgeIdx, -1)) return false; }
                }
            }
            // Apply Left outer edges (r=0..3, c=-1 => H edges)
            for (int r_out = 0; r_out < 4; r_out++) {
                int bit = 32 + r_out;
                int rr = r + r_out;
                int cc = c - 1;
                if (rr >= 0 && rr <= rows && cc >= 0 && cc < cols) {
                    int edgeIdx = getHEdgeIndex(rr, cc);
                    if ((fl >> bit) & 1) { if (!setEdgeState(edgeIdx, 1)) return false; }
                    if (!((fc >> bit) & 1)) { if (!setEdgeState(edgeIdx, -1)) return false; }
                }
            }
            // Apply Right outer edges (r=0..3, c=3 => H edges)
            for (int r_out = 0; r_out < 4; r_out++) {
                int bit = 36 + r_out;
                int rr = r + r_out;
                int cc = c + 3;
                if (rr >= 0 && rr <= rows && cc >= 0 && cc < cols) {
                    int edgeIdx = getHEdgeIndex(rr, cc);
                    if ((fl >> bit) & 1) { if (!setEdgeState(edgeIdx, 1)) return false; }
                    if (!((fc >> bit) & 1)) { if (!setEdgeState(edgeIdx, -1)) return false; }
                }
            }
        }
    }

    return true;
}

#endif

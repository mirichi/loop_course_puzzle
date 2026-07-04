#ifndef LUT1X2_MODULE_H
#define LUT1X2_MODULE_H

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
int8_t getEdgeState(int edgeIdx);

uint32_t* lut1x2 = NULL;

void init_lut1x2() {
    if (lut1x2 != NULL) return;
    
    int num_states = 19683; // 3^9
    lut1x2 = (uint32_t*)malloc(25 * num_states * sizeof(uint32_t));
    
    int num_valid_configs[25];
    int valid_configs[25][512];
    
    for (int c0 = 0; c0 <= 4; c0++) {
        for (int c1 = 0; c1 <= 4; c1++) {
            int clueIdx = c0 * 5 + c1;
            num_valid_configs[clueIdx] = 0;
            
            for (int mask = 0; mask < 512; mask++) {
                int e[9];
                for (int i = 0; i < 9; i++) e[i] = (mask >> i) & 1;
                
                // Vertex degree checks
                int v01 = e[0] + e[1] + e[5] + e[7];
                if (v01 != 0 && v01 != 2) continue;
                
                int v11 = e[2] + e[3] + e[5] + e[8];
                if (v11 != 0 && v11 != 2) continue;
                
                // Clue checks
                int lines0 = e[0] + e[2] + e[4] + e[5];
                if (c0 != 4 && lines0 != c0) continue;
                
                int lines1 = e[1] + e[3] + e[5] + e[6];
                if (c1 != 4 && lines1 != c1) continue;
                
                valid_configs[clueIdx][num_valid_configs[clueIdx]++] = mask;
            }
        }
    }
    
    for (int clueIdx = 0; clueIdx < 25; clueIdx++) {
        for (int state = 0; state < num_states; state++) {
            int s[9];
            int temp = state;
            for (int i = 0; i < 9; i++) {
                s[i] = temp % 3;
                temp /= 3;
            }
            
            uint32_t AND_mask = 0x1FF;
            uint32_t OR_mask = 0;
            int valid_count = 0;
            
            for (int i = 0; i < num_valid_configs[clueIdx]; i++) {
                int mask = valid_configs[clueIdx][i];
                bool compatible = true;
                for (int e = 0; e < 9; e++) {
                    int m = (mask >> e) & 1;
                    if (s[e] == 1 && m == 0) { compatible = false; break; } // Requires line, mask has cross
                    if (s[e] == 2 && m == 1) { compatible = false; break; } // Requires cross, mask has line
                }
                if (compatible) {
                    AND_mask &= mask;
                    OR_mask |= mask;
                    valid_count++;
                }
            }
            
            uint32_t result = 0;
            if (valid_count == 0) {
                result = 0x80000000; // Invalid state
            } else {
                uint32_t forced_lines = AND_mask;
                uint32_t forced_crosses = (~OR_mask) & 0x1FF;
                
                // Filter out already known states
                for (int e = 0; e < 9; e++) {
                    if (s[e] == 1) forced_lines &= ~(1 << e);
                    if (s[e] == 2) forced_crosses &= ~(1 << e);
                }
                result = forced_lines | (forced_crosses << 9);
            }
            lut1x2[clueIdx * num_states + state] = result;
        }
    }
}

bool applyLUT1x2(bool* changed) {
    if (lut1x2 == NULL) return true;
    
    int num_states = 19683;
    
    // Horizontal 1x2 passes
    for (int r = 0; r < rows; r++) {
        for (int c = 0; c < cols - 1; c++) {
            int c0 = clues[r * cols + c];
            if (c0 == -1) c0 = 4;
            int c1 = clues[r * cols + c + 1];
            if (c1 == -1) c1 = 4;
            int clueIdx = c0 * 5 + c1;
            
            int edge_indices[9] = {
                getHEdgeIndex(r, c),         // e0: Top C0
                getHEdgeIndex(r, c + 1),     // e1: Top C1
                getHEdgeIndex(r + 1, c),     // e2: Bottom C0
                getHEdgeIndex(r + 1, c + 1), // e3: Bottom C1
                getVEdgeIndex(r, c),         // e4: Left C0
                getVEdgeIndex(r, c + 1),     // e5: Mid V
                getVEdgeIndex(r, c + 2),     // e6: Right C1
                getVEdgeIndex(r - 1, c + 1), // e7: Up from Mid
                getVEdgeIndex(r + 1, c + 1)  // e8: Down from Mid
            };
            
            int state = 0;
            int pow_idx = 1;
            for (int i = 0; i < 9; i++) {
                int s_val = 0; // 0=Unknown, 1=Line, 2=Cross
                int idx = edge_indices[i];
                if (idx == -1) {
                    s_val = 2; // Outside grid is always a cross
                } else {
                    int8_t st = getEdgeState(idx);
                    if (st == 1) s_val = 1;
                    else if (st == -1) s_val = 2;
                }
                state += s_val * pow_idx;
                pow_idx *= 3;
            }
            
            uint32_t result = lut1x2[clueIdx * num_states + state];
            if (result & 0x80000000) return false; // Contradiction
            
            if (result != 0) {
                // Apply forced lines
                for (int i = 0; i < 9; i++) {
                    if ((result >> i) & 1) {
                        int idx = edge_indices[i];
                        if (idx != -1) {
                            if (!setEdgeState(idx, 1)) return false;
                            *changed = true;
                        }
                    }
                }
                // Apply forced crosses
                for (int i = 0; i < 9; i++) {
                    if ((result >> (i + 9)) & 1) {
                        int idx = edge_indices[i];
                        if (idx != -1) {
                            if (!setEdgeState(idx, -1)) return false;
                            *changed = true;
                        }
                    }
                }
            }
        }
    }
    
    // Vertical 1x2 passes (mapped onto the same horizontal LUT)
    for (int r = 0; r < rows - 1; r++) {
        for (int c = 0; c < cols; c++) {
            int c0 = clues[r * cols + c];
            if (c0 == -1) c0 = 4;
            int c1 = clues[(r + 1) * cols + c];
            if (c1 == -1) c1 = 4;
            int clueIdx = c0 * 5 + c1;
            
            int edge_indices[9] = {
                getVEdgeIndex(r, c),         // mapped to e0
                getVEdgeIndex(r + 1, c),     // mapped to e1
                getVEdgeIndex(r, c + 1),     // mapped to e2
                getVEdgeIndex(r + 1, c + 1), // mapped to e3
                getHEdgeIndex(r, c),         // mapped to e4
                getHEdgeIndex(r + 1, c),     // mapped to e5
                getHEdgeIndex(r + 2, c),     // mapped to e6
                getHEdgeIndex(r + 1, c - 1), // mapped to e7
                getHEdgeIndex(r + 1, c + 1)  // mapped to e8
            };
            
            int state = 0;
            int pow_idx = 1;
            for (int i = 0; i < 9; i++) {
                int s_val = 0;
                int idx = edge_indices[i];
                if (idx == -1) {
                    s_val = 2;
                } else {
                    int8_t st = getEdgeState(idx);
                    if (st == 1) s_val = 1;
                    else if (st == -1) s_val = 2;
                }
                state += s_val * pow_idx;
                pow_idx *= 3;
            }
            
            uint32_t result = lut1x2[clueIdx * num_states + state];
            if (result & 0x80000000) return false;
            
            if (result != 0) {
                // Apply forced lines
                for (int i = 0; i < 9; i++) {
                    if ((result >> i) & 1) {
                        int idx = edge_indices[i];
                        if (idx != -1) {
                            if (!setEdgeState(idx, 1)) return false;
                            *changed = true;
                        }
                    }
                }
                // Apply forced crosses
                for (int i = 0; i < 9; i++) {
                    if ((result >> (i + 9)) & 1) {
                        int idx = edge_indices[i];
                        if (idx != -1) {
                            if (!setEdgeState(idx, -1)) return false;
                            *changed = true;
                        }
                    }
                }
            }
        }
    }
    
    return true;
}

#endif

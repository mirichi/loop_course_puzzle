/**
 * Loop Course Puzzle Generator
 * Generates beautiful, logically solvable Loop Course puzzles of different difficulties.
 */
class LoopCourseGenerator {
  constructor(rows, cols) {
    this.rows = rows;
    this.cols = cols;
  }

  // Generates a random valid loop using cell partition (Inside / Outside) expansion.
  // Returns a 2D array representing the state of each edge in the generated loop:
  // 1 if part of the loop, -1 if not.
  generateRandomLoop() {
    const numSectorsX = this.cols >= 24 ? 4 : (this.cols >= 8 ? 3 : 2);
    const numSectorsY = this.rows >= 12 ? 4 : (this.rows >= 8 ? 3 : 2);

    const checkSectorCoverage = (tempCells) => {
      const sectors = Array.from({ length: numSectorsY }, () => new Array(numSectorsX).fill(false));
      for (let r = 0; r < this.rows; r++) {
        for (let c = 0; c < this.cols; c++) {
          if (tempCells[r][c] === 1) {
            const sy = Math.floor(r * numSectorsY / this.rows);
            const sx = Math.floor(c * numSectorsX / this.cols);
            if (sy >= 0 && sy < numSectorsY && sx >= 0 && sx < numSectorsX) {
              sectors[sy][sx] = true;
            }
          }
        }
      }
      for (let sy = 0; sy < numSectorsY; sy++) {
        for (let sx = 0; sx < numSectorsX; sx++) {
          if (!sectors[sy][sx]) return false;
        }
      }
      return true;
    };

    const count3x3OutsideBlocks = (tempCells) => {
      let count = 0;
      for (let r = 0; r < this.rows - 2; r++) {
        for (let c = 0; c < this.cols - 2; c++) {
          let isAllOutside = true;
          for (let i = 0; i < 3; i++) {
            for (let j = 0; j < 3; j++) {
              if (tempCells[r + i][c + j] !== 0) {
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
    };

    const checkOutsideConnectivity = (tempCells) => {
      const visited = Array.from({ length: this.rows }, () => new Array(this.cols).fill(false));
      let outsideCount = 0;
      const queue = [];
      
      // Seed queue with all Outside cells on the grid boundary
      for (let r = 0; r < this.rows; r++) {
        for (let c = 0; c < this.cols; c++) {
          if (tempCells[r][c] === 0) {
            outsideCount++;
            const isBorder = (r === 0 || r === this.rows - 1 || c === 0 || c === this.cols - 1);
            if (isBorder) {
              queue.push([r, c]);
              visited[r][c] = true;
            }
          }
        }
      }
      
      if (outsideCount === 0) return false;
      if (queue.length === 0 && outsideCount > 0) {
        return false;
      }
      
      // BFS to flood fill Outside cells from the border
      let reachedCount = 0;
      const dr = [-1, 1, 0, 0];
      const dc = [0, 0, -1, 1];
      
      while (queue.length > 0) {
        const [r, c] = queue.shift();
        reachedCount++;
        
        for (let i = 0; i < 4; i++) {
          const nr = r + dr[i];
          const nc = c + dc[i];
          
          if (nr >= 0 && nr < this.rows && nc >= 0 && nc < this.cols) {
            if (tempCells[nr][nc] === 0 && !visited[nr][nc]) {
              visited[nr][nc] = true;
              queue.push([nr, nc]);
            }
          }
        }
      }
      
      return reachedCount === outsideCount;
    };

    let attempts = 0;
    const maxAttempts = 40;
    let finalCells = null;

    while (attempts < maxAttempts) {
      attempts++;
      const cells = Array.from({ length: this.rows }, () => new Array(this.cols).fill(0)); // 0 = Outside, 1 = Inside
      
      // Pick a random starting cell
      const startR = Math.floor(Math.random() * this.rows);
      const startC = Math.floor(Math.random() * this.cols);
      cells[startR][startC] = 1;
      
      // Fill ratio: determine how many cells will be "Inside" the loop
      // Dynamically adjust fill ratio based on grid size to prevent border-sticking on small grids
      const totalCells = this.rows * this.cols;
      let fillRatioMin = 0.72;
      let fillRatioMax = 0.87;
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
      
      const targetInsideCount = Math.floor(totalCells * (fillRatioMin + Math.random() * (fillRatioMax - fillRatioMin)));
      let insideCount = 1;
      
      let failedAttempts = 0;
      const maxFailedAttempts = 300; // Increased to give ample attempts to break 2x2 blocks
      const dr = [-1, 1, 0, 0];
      const dc = [0, 0, -1, 1];
      
      // Grow while insideCount is below target OR (for large boards) there are still 3x3 blocks of outside (empty) space to break
      const shouldBreakOutside = (totalCells >= 100);
      while ((insideCount < targetInsideCount || (shouldBreakOutside && count3x3OutsideBlocks(cells) > 0)) && failedAttempts < maxFailedAttempts) {
        const candidates = [];
        
        // Calculate center of mass of current Inside cells
        let sumR = 0, sumC = 0;
        for (let r = 0; r < this.rows; r++) {
          for (let c = 0; c < this.cols; c++) {
            if (cells[r][c] === 1) {
              sumR += r;
              sumC += c;
            }
          }
        }
        const avgR = sumR / insideCount;
        const avgC = sumC / insideCount;
        
        // Calculate sector counts to give unexplored sector bonuses
        const sectorCounts = Array.from({ length: numSectorsY }, () => new Array(numSectorsX).fill(0));
        for (let r = 0; r < this.rows; r++) {
          for (let c = 0; c < this.cols; c++) {
            if (cells[r][c] === 1) {
              const sy = Math.floor(r * numSectorsY / this.rows);
              const sx = Math.floor(c * numSectorsX / this.cols);
              if (sy >= 0 && sy < numSectorsY && sx >= 0 && sx < numSectorsX) {
                sectorCounts[sy][sx]++;
              }
            }
          }
        }
        
        for (let r = 0; r < this.rows; r++) {
          for (let c = 0; c < this.cols; c++) {
            if (cells[r][c] === 0) {
              let insideNeighbors = 0;
              let firstInsideNeighbor = null;
              for (let i = 0; i < 4; i++) {
                const nr = r + dr[i];
                const nc = c + dc[i];
                if (nr >= 0 && nr < this.rows && nc >= 0 && nc < this.cols && cells[nr][nc] === 1) {
                  insideNeighbors++;
                  if (!firstInsideNeighbor) {
                    firstInsideNeighbor = [nr, nc];
                  }
                }
              }
              
              const wouldForm4x4Inside = () => {
                const isInside = (ir, ic) => {
                  if (ir < 0 || ir >= this.rows || ic < 0 || ic >= this.cols) return false;
                  return cells[ir][ic] === 1;
                };
                for (let dr = -3; dr <= 0; dr++) {
                  for (let dc = -3; dc <= 0; dc++) {
                    let count = 0;
                    for (let i = 0; i < 4; i++) {
                      for (let j = 0; j < 4; j++) {
                        const nr = r + dr + i;
                        const nc = c + dc + j;
                        if (nr === r && nc === c) continue;
                        if (isInside(nr, nc)) {
                          count++;
                        }
                      }
                    }
                    if (count === 15) return true;
                  }
                }
                return false;
              };
              
              if (insideNeighbors > 0 && insideNeighbors < 4 && !wouldForm4x4Inside()) {
                const neighborScore = (insideNeighbors === 1) ? 35 : ((insideNeighbors === 2) ? 5 : 1);
                
                const dist = Math.pow(r - avgR, 2) + Math.pow(c - avgC, 2);
                const distScore = 1.0 + dist * 0.15;
                
                const isBorder = (r === 0 || r === this.rows - 1 || c === 0 || c === this.cols - 1);
                // Discourage border sticking on small grids by applying a penalty
                const borderPenalty = (totalCells <= 64 && isBorder) ? 0.35 : 1.0;
                
                let bendMultiplier = 1.0;
                if (insideNeighbors === 1 && firstInsideNeighbor) {
                  const [nr, nc] = firstInsideNeighbor;
                  const secondNeighbors = [];
                  for (let j = 0; j < 4; j++) {
                    const nnr = nr + dr[j];
                    const nnc = nc + dc[j];
                    if (nnr >= 0 && nnr < this.rows && nnc >= 0 && nnc < this.cols) {
                      if (cells[nnr][nnc] === 1) {
                        secondNeighbors.push([nnr, nnc]);
                      }
                    }
                  }
                  
                  if (secondNeighbors.length === 1) {
                    const [nnr, nnc] = secondNeighbors[0];
                    const isCollinear = (r === nr && nr === nnr) || (c === nc && nc === nnc);
                    if (isCollinear) {
                      bendMultiplier = 0.3; // Balanced straight penalty
                    } else {
                      bendMultiplier = 2.0; // Balanced bending bonus
                    }
                  }
                }
                
                let sectorBonus = 1.0;
                const sy = Math.floor(r * numSectorsY / this.rows);
                const sx = Math.floor(c * numSectorsX / this.cols);
                if (sy >= 0 && sy < numSectorsY && sx >= 0 && sx < numSectorsX) {
                  if (sectorCounts[sy][sx] === 0) {
                    sectorBonus = 6.0; // Dynamic pull to empty sectors
                  }
                }
                
                // 3x3 Outside Block Breaker Bonus: actively eliminate empty spaces
                const isOutside = (br, bc) => {
                  if (br < 0 || br >= this.rows || bc < 0 || bc >= this.cols) return false;
                  return cells[br][bc] === 0;
                };
                let brokenOutsideBlocks = 0;
                // Check 9 possible 3x3 blocks that (r, c) can break:
                for (let dr = -2; dr <= 0; dr++) {
                  for (let dc = -2; dc <= 0; dc++) {
                    let isAllOutside = true;
                    for (let i = 0; i < 3; i++) {
                      for (let j = 0; j < 3; j++) {
                        const nr = r + dr + i;
                        const nc = c + dc + j;
                        if (nr === r && nc === c) continue;
                        if (!isOutside(nr, nc)) {
                          isAllOutside = false;
                          break;
                        }
                      }
                      if (!isAllOutside) break;
                    }
                    if (isAllOutside) brokenOutsideBlocks++;
                  }
                }
                
                let breakerBonus = 1.0;
                if (brokenOutsideBlocks > 0) {
                  breakerBonus = 1.0 + 8.0 * brokenOutsideBlocks; // Strong pull to destroy empty spaces
                }
                
                const score = neighborScore * distScore * borderPenalty * bendMultiplier * sectorBonus * breakerBonus;
                candidates.push({ r, c, score });
              }
            }
          }
        }
        
        if (candidates.length === 0) break;
        
        candidates.sort((a, b) => b.score - a.score);
        
        const poolSize = Math.min(3, candidates.length);
        const chosen = candidates[Math.floor(Math.random() * poolSize)];
        const cr = chosen.r;
        const cc = chosen.c;
        
        cells[cr][cc] = 1;
        
        // Auto Hole Filling: find any unreached Outside cells and turn them into Inside cells
        const filledCoords = [];
        const visited = Array.from({ length: this.rows }, () => new Array(this.cols).fill(false));
        const queue = [];
        for (let r = 0; r < this.rows; r++) {
          for (let c = 0; c < this.cols; c++) {
            if (cells[r][c] === 0) {
              const isBorder = (r === 0 || r === this.rows - 1 || c === 0 || c === this.cols - 1);
              if (isBorder) {
                queue.push([r, c]);
                visited[r][c] = true;
              }
            }
          }
        }
        
        const drB = [-1, 1, 0, 0];
        const dcB = [0, 0, -1, 1];
        while (queue.length > 0) {
          const [r, c] = queue.shift();
          for (let i = 0; i < 4; i++) {
            const nr = r + drB[i];
            const nc = c + dcB[i];
            if (nr >= 0 && nr < this.rows && nc >= 0 && nc < this.cols) {
              if (cells[nr][nc] === 0 && !visited[nr][nc]) {
                visited[nr][nc] = true;
                queue.push([nr, nc]);
              }
            }
          }
        }
        
        // Temporarily fill unreached Outside cells (holes)
        for (let r = 0; r < this.rows; r++) {
          for (let c = 0; c < this.cols; c++) {
            if (cells[r][c] === 0 && !visited[r][c]) {
              cells[r][c] = 1;
              filledCoords.push([r, c]);
            }
          }
        }
        
        // Verify 3x3 Inside constraint after filling holes
        const has4x4Inside = () => {
          for (let r = 0; r < this.rows - 3; r++) {
            for (let c = 0; c < this.cols - 3; c++) {
              let isAllInside = true;
              for (let i = 0; i < 4; i++) {
                for (let j = 0; j < 4; j++) {
                  if (cells[r + i][c + j] !== 1) {
                    isAllInside = false;
                    break;
                  }
                }
                if (!isAllInside) break;
              }
              if (isAllInside) return true;
            }
          }
          return false;
        };
        
        if (!has4x4Inside()) {
          insideCount += 1 + filledCoords.length;
          failedAttempts = 0;
        } else {
          // Revert candidate and all filled holes
          cells[cr][cc] = 0;
          for (const [fr, fc] of filledCoords) {
            cells[fr][fc] = 0;
          }
          failedAttempts++;
        }
      }
      
      finalCells = cells;
      const minAcceptableInsideCount = Math.floor(targetInsideCount * 0.9);
      if (insideCount >= minAcceptableInsideCount && checkSectorCoverage(cells)) {
        break; // Success! We satisfy both fill coverage and sector check
      }
    }
    
    const cells = finalCells;
    
    // Translate the cells partition to loop edges
    // An edge is in the loop if it divides an Inside cell (1) from an Outside cell (0).
    const numH = (this.rows + 1) * this.cols;
    const numV = this.rows * (this.cols + 1);
    const numEdges = numH + numV;
    const loopEdges = new Array(numEdges).fill(-1);
    
    // Helper to get cell state (returns 0 if out of bounds)
    const getCell = (r, c) => {
      if (r < 0 || r >= this.rows || c < 0 || c >= this.cols) return 0;
      return cells[r][c];
    };
    
    // Horizontal edges
    for (let r = 0; r <= this.rows; r++) {
      for (let c = 0; c < this.cols; c++) {
        const topCell = getCell(r - 1, c);
        const bottomCell = getCell(r, c);
        const idx = r * this.cols + c;
        if (topCell !== bottomCell) {
          loopEdges[idx] = 1; // Part of loop
        }
      }
    }
    
    // Vertical edges
    for (let r = 0; r < this.rows; r++) {
      for (let c = 0; c <= this.cols; c++) {
        const leftCell = getCell(r, c - 1);
        const rightCell = getCell(r, c);
        const idx = numH + r * (this.cols + 1) + c;
        if (leftCell !== rightCell) {
          loopEdges[idx] = 1; // Part of loop
        }
      }
    }
    
    return { cells, loopEdges };
  }

  // Calculate cell clues from a loop
  calculateClues(cells) {
    const clues = Array.from({ length: this.rows }, () => new Array(this.cols).fill(null));
    
    const getCell = (r, c) => {
      if (r < 0 || r >= this.rows || c < 0 || c >= this.cols) return 0;
      return cells[r][c];
    };

    for (let r = 0; r < this.rows; r++) {
      for (let c = 0; c < this.cols; c++) {
        const state = cells[r][c];
        let edgeCount = 0;
        
        // Check top, bottom, left, right cell transitions
        if (state !== getCell(r - 1, c)) edgeCount++;
        if (state !== getCell(r + 1, c)) edgeCount++;
        if (state !== getCell(r, c - 1)) edgeCount++;
        if (state !== getCell(r, c + 1)) edgeCount++;
        
        clues[r][c] = edgeCount;
      }
    }
    
    return clues;
  }

  /**
   * Generates a puzzle
   * @param {string} difficulty - 'easy', 'medium', or 'hard'
   * @returns {object} { clues, solution }
   */
  generate(difficulty = 'medium') {
    // Step 1: Generate a random loop and corresponding clues
    let { cells, loopEdges } = this.generateRandomLoop();
    let originalClues = this.calculateClues(cells);
    
    // Copy clues for editing
    const clues = originalClues.map(row => [...row]);
    
    // Step 2: Minimize clues while keeping solution unique
    // Create a list of cell coordinates
    const cellCoords = [];
    for (let r = 0; r < this.rows; r++) {
      for (let c = 0; c < this.cols; c++) {
        cellCoords.push([r, c]);
      }
    }
    
    // Shuffle the cell coordinates first for randomness within groups
    for (let i = cellCoords.length - 1; i > 0; i--) {
      const j = Math.floor(Math.random() * (i + 1));
      [cellCoords[i], cellCoords[j]] = [cellCoords[j], cellCoords[i]];
    }
    
    // Sort cell coordinates to prioritize hiding 0s and keeping 3s:
    // 0s first (try to hide first, making them disappear)
    // 1s and 2s next
    // 3s last (try to hide last, making them stay on the board)
    cellCoords.sort((a, b) => {
      const clueA = originalClues[a[0]][a[1]];
      const clueB = originalClues[b[0]][b[1]];
      
      const getPriority = (clue) => {
        if (clue === 0) return 0; // Hide first!
        if (clue === 3) return 2; // Keep last!
        return 1; // 1 and 2
      };
      
      return getPriority(clueA) - getPriority(clueB);
    });
    
    // Adjust target parameters based on difficulty
    let keepRatio = 0.45; // Default for easy
    if (difficulty === 'medium') keepRatio = 0.32;
    if (difficulty === 'hard') keepRatio = 0.22;
    
    const targetKeepCount = Math.floor(this.rows * this.cols * keepRatio);
    let currentClueCount = this.rows * this.cols;
    
    for (const [r, c] of cellCoords) {
      if (currentClueCount <= targetKeepCount) {
        break; // Reached target clue count for this difficulty
      }
      
      const originalClue = clues[r][c];
      
      // If we are on easy, let's keep some 3s as they are great starting anchors (no 0 anchors!)
      if (difficulty === 'easy' && originalClue === 3 && Math.random() < 0.8) {
        continue;
      }
      
      // Temporarily remove clue
      clues[r][c] = null;
      currentClueCount--;
      
      // Fast logical solvability checker
      const checkSolvability = () => {
        const solver = new window.LoopCourseSolver(this.rows, this.cols, clues);
        
        // 1. Run the super fast logical deduction engine
        const success = solver.deduct();
        if (!success) return false; // Contradiction
        
        // If deduction solved the board completely, it is logically solvable (perfect unique solution)!
        if (solver.isSolved()) return true;
        
        // For Medium/Hard, allow a tiny, ultra-shallow backtracking search to handle minor logic chains
        const totalCells = this.rows * this.cols;
        let maxSteps = (difficulty === 'easy') ? 0 : 50; 
        if (totalCells > 150) {
          maxSteps = (difficulty === 'easy') ? 0 : 15; // Reduce backtracking depth for huge grids to keep generation fast
        }
        if (maxSteps === 0) return false; // Easy puzzles must be solvable by pure deduction!
        
        let solutions = [];
        let steps = 0;
        
        const backtrack = () => {
          steps++;
          if (steps > maxSteps) {
            solutions.push("timeout");
            return;
          }
          
          const backup = [...solver.edgeStates];
          if (!solver.deduct()) {
            solver.edgeStates = backup;
            return;
          }
          
          if (solver.isSolved()) {
            solutions.push([...solver.edgeStates]);
            solver.edgeStates = backup;
            return;
          }
          
          const undecidedIdx = solver.edgeStates.indexOf(0);
          if (undecidedIdx === -1) {
            solver.edgeStates = backup;
            return;
          }
          
          if (solutions.length >= 2) {
            solver.edgeStates = backup;
            return;
          }
          
          let branchIdx = undecidedIdx;
          outer: for (let r = 0; r < solver.rows; r++) {
            for (let c = 0; c < solver.cols; c++) {
              if (solver.clues[r][c] !== null) {
                const cellEdges = solver.getCellEdges(r, c);
                for (const idx of cellEdges) {
                  if (solver.edgeStates[idx] === 0) {
                    branchIdx = idx;
                    break outer;
                  }
                }
              }
            }
          }
          
          solver.edgeStates[branchIdx] = 1;
          backtrack();
          
          if (solutions.length >= 2) {
            solver.edgeStates = backup;
            return;
          }
          
          solver.edgeStates[branchIdx] = -1;
          backtrack();
          
          solver.edgeStates = backup;
        };
        
        backtrack();
        return solutions.length === 1 && solutions[0] !== "timeout";
      };
      
      // If hiding this clue makes the puzzle unsolvable or non-unique, restore it!
      if (!checkSolvability()) {
        clues[r][c] = originalClue;
        currentClueCount++;
      }
    }
    
    return {
      clues,
      solution: loopEdges
    };
  }
}

// Bind to window for local file protocol compatibility without modules
window.LoopCourseGenerator = LoopCourseGenerator;

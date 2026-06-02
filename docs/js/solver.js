/**
 * Loop Course Puzzle Solver
 * Provides logic-based deduction and backtracking search to solve Loop Course puzzles.
 * Can detect if a puzzle has 0, 1, or multiple solutions.
 */
class LoopCourseSolver {
  constructor(rows, cols, clues) {
    this.rows = rows;
    this.cols = cols;
    this.clues = clues; // 2D array of size rows x cols, with numbers 0-3 or null
    
    this.numH = (rows + 1) * cols;
    this.numV = rows * (cols + 1);
    this.numEdges = this.numH + this.numV;
    this.numDots = (rows + 1) * (cols + 1);
    
    this.edgeStates = new Int8Array(this.numEdges); // 0 = empty, 1 = line, -1 = cross
    
    // Pre-allocate backup arrays for backtracking search (avoids constant GC load and heavy memory allocation)
    this.maxBackupDepth = 200;
    this.backupStack = Array.from({ length: this.maxBackupDepth }, () => new Int8Array(this.numEdges));
    this.strict = false;
    
    // Pre-allocate DSU arrays for cycle pruning
    this.dsuParent = new Int32Array(this.numDots);
    this.dsuRank = new Int32Array(this.numDots);
    this.dsuHistory = [];
    this.backupAfterDeductStack = Array.from({ length: this.maxBackupDepth }, () => new Int8Array(this.numEdges));
    
    // Pre-allocate queues for AC-3 propagation
    this.cellQueue = new Int32Array(this.rows * this.cols * 4);
    this.cellQueueHead = 0;
    this.cellQueueTail = 0;
    this.cellInQueue = new Uint8Array(this.rows * this.cols);
    
    this.dotQueue = new Int32Array(this.numDots * 4);
    this.dotQueueHead = 0;
    this.dotQueueTail = 0;
    this.dotInQueue = new Uint8Array(this.numDots);
  }

  // DSU Helper Methods
  dsuInit() {
    for (let i = 0; i < this.numDots; i++) {
      this.dsuParent[i] = i;
      this.dsuRank[i] = 0;
    }
    this.dsuHistory.length = 0;
  }

  dsuInitFromCurrent() {
    this.dsuInit();
    for (let i = 0; i < this.numEdges; i++) {
      if (this.edgeStates[i] === 1) {
        let dotA, dotB;
        if (i < this.numH) {
          const r = Math.floor(i / this.cols);
          const c = i % this.cols;
          dotA = r * (this.cols + 1) + c;
          dotB = dotA + 1;
        } else {
          const vIdx = i - this.numH;
          const r = Math.floor(vIdx / (this.cols + 1));
          const c = vIdx % (this.cols + 1);
          dotA = r * (this.cols + 1) + c;
          dotB = dotA + (this.cols + 1);
        }
        this.dsuUnion(dotA, dotB);
      }
    }
  }

  dsuFind(i) {
    while (i !== this.dsuParent[i]) {
      i = this.dsuParent[i];
    }
    return i;
  }

  dsuUnion(u, v) {
    const rootU = this.dsuFind(u);
    const rootV = this.dsuFind(v);
    if (rootU === rootV) {
      return false; // Cycle detected!
    }
    
    this.dsuHistory.push({ node: rootU, parent: this.dsuParent[rootU], rank: this.dsuRank[rootU] });
    this.dsuHistory.push({ node: rootV, parent: this.dsuParent[rootV], rank: this.dsuRank[rootV] });
    
    if (this.dsuRank[rootU] < this.dsuRank[rootV]) {
      this.dsuParent[rootU] = rootV;
    } else if (this.dsuRank[rootU] > this.dsuRank[rootV]) {
      this.dsuParent[rootV] = rootU;
    } else {
      this.dsuParent[rootU] = rootV;
      this.dsuRank[rootV]++;
    }
    return true;
  }

  dsuRollback(checkpoint) {
    while (this.dsuHistory.length > checkpoint) {
      const save = this.dsuHistory.pop();
      this.dsuParent[save.node] = save.parent;
      this.dsuRank[save.node] = save.rank;
    }
  }

  // Queue Helper Methods
  enqueueCell(r, c) {
    if (r < 0 || r >= this.rows || c < 0 || c >= this.cols) return;
    const idx = r * this.cols + c;
    if (this.clues[r][c] === null) return; // Only process cells with clues to match C
    if (!this.cellInQueue[idx]) {
      this.cellQueue[this.cellQueueTail++] = idx;
      if (this.cellQueueTail >= this.cellQueue.length) this.cellQueueTail = 0;
      this.cellInQueue[idx] = 1;
    }
  }

  dequeueCell() {
    if (this.cellQueueHead === this.cellQueueTail) return -1;
    const idx = this.cellQueue[this.cellQueueHead++];
    if (this.cellQueueHead >= this.cellQueue.length) this.cellQueueHead = 0;
    this.cellInQueue[idx] = 0;
    return idx;
  }

  enqueueDot(r, c) {
    if (r < 0 || r > this.rows || c < 0 || c > this.cols) return;
    const idx = r * (this.cols + 1) + c;
    if (!this.dotInQueue[idx]) {
      this.dotQueue[this.dotQueueTail++] = idx;
      if (this.dotQueueTail >= this.dotQueue.length) this.dotQueueTail = 0;
      this.dotInQueue[idx] = 1;
    }
  }

  dequeueDot() {
    if (this.dotQueueHead === this.dotQueueTail) return -1;
    const idx = this.dotQueue[this.dotQueueHead++];
    if (this.dotQueueHead >= this.dotQueue.length) this.dotQueueHead = 0;
    this.dotInQueue[idx] = 0;
    return idx;
  }

  clearQueues() {
    this.cellQueueHead = 0;
    this.cellQueueTail = 0;
    this.cellInQueue.fill(0);
    
    this.dotQueueHead = 0;
    this.dotQueueTail = 0;
    this.dotInQueue.fill(0);
  }

  // Coordinate mapping utilities
  getHEdgeIndex(r, c) {
    if (r < 0 || r > this.rows || c < 0 || c >= this.cols) return -1;
    return r * this.cols + c;
  }

  getVEdgeIndex(r, c) {
    if (r < 0 || r >= this.rows || c < 0 || c > this.cols) return -1;
    return this.numH + r * (this.cols + 1) + c;
  }

  // Returns array of 4 edge indices around cell (r, c)
  getCellEdges(r, c) {
    // Inlined for performance to avoid function overhead and bounds checks
    const top = r * this.cols + c;
    const right = this.numH + r * (this.cols + 1) + (c + 1);
    const bottom = (r + 1) * this.cols + c;
    const left = this.numH + r * (this.cols + 1) + c;
    return [top, right, bottom, left];
  }

  // Returns array of up to 4 edge indices connected to dot (r, c)
  getDotEdges(r, c) {
    const edges = [];
    // Up
    if (r > 0) edges.push(this.numH + (r - 1) * (this.cols + 1) + c);
    // Down
    if (r < this.rows) edges.push(this.numH + r * (this.cols + 1) + c);
    // Left
    if (c > 0) edges.push(r * this.cols + (c - 1));
    // Right
    if (c < this.cols) edges.push(r * this.cols + c);
    return edges;
  }

  // Set edge state with DSU cycle pruning and enqueue affected items
  setEdgeState(edgeIdx, state) {
    if (this.edgeStates[edgeIdx] === state) return true;
    if (this.edgeStates[edgeIdx] !== 0) return false; // Contradiction
    
    if (state === 1) {
      let dotA, dotB;
      if (edgeIdx < this.numH) {
        const r = Math.floor(edgeIdx / this.cols);
        const c = edgeIdx % this.cols;
        dotA = r * (this.cols + 1) + c;
        dotB = dotA + 1;
      } else {
        const vIdx = edgeIdx - this.numH;
        const r = Math.floor(vIdx / (this.cols + 1));
        const c = vIdx % (this.cols + 1);
        dotA = r * (this.cols + 1) + c;
        dotB = dotA + (this.cols + 1);
      }
      if (!this.dsuUnion(dotA, dotB)) {
        // Cycle closed! Check if it's solved
        this.edgeStates[edgeIdx] = 1;
        const solved = this.isSolved(false); // strict=false as in C
        this.edgeStates[edgeIdx] = 0;
        if (!solved) {
          return false; // Contradiction: Premature loop closed!
        }
      }
    }
    
    this.edgeStates[edgeIdx] = state;
    
    if (edgeIdx < this.numH) {
      const r = Math.floor(edgeIdx / this.cols);
      const c = edgeIdx % this.cols;
      this.enqueueCell(r - 1, c);
      this.enqueueCell(r, c);
      this.enqueueDot(r, c);
      this.enqueueDot(r, c + 1);
    } else {
      const vIdx = edgeIdx - this.numH;
      const r = Math.floor(vIdx / (this.cols + 1));
      const c = vIdx % (this.cols + 1);
      this.enqueueCell(r, c - 1);
      this.enqueueCell(r, c);
      this.enqueueDot(r, c);
      this.enqueueDot(r + 1, c);
    }
    return true;
  }

  // Run logical deduction rules repeatedly until no more progress is made
  // Returns false if a contradiction is found, true otherwise
  deduct() {
    this.dsuInitFromCurrent();
    this.clearQueues();
    
    // Seed queues with all cells and dots
    for (let r = 0; r < this.rows; r++) {
      for (let c = 0; c < this.cols; c++) {
        this.enqueueCell(r, c);
      }
    }
    for (let r = 0; r <= this.rows; r++) {
      for (let c = 0; c <= this.cols; c++) {
        this.enqueueDot(r, c);
      }
    }
    
    return this.deductIncremental();
  }

  // AC-3 local constraint propagation loop
  deductIncremental() {
    while (this.cellQueueHead !== this.cellQueueTail || this.dotQueueHead !== this.dotQueueTail) {
      const cellIdx = this.dequeueCell();
      if (cellIdx !== -1) {
        const r = Math.floor(cellIdx / this.cols);
        const c = cellIdx % this.cols;
        const clue = this.clues[r][c];
        
        if (clue !== null) {
          const cellEdges = this.getCellEdges(r, c);
          let lines = 0;
          let crosses = 0;
          const undecided = [];
          
          for (const idx of cellEdges) {
            if (this.edgeStates[idx] === 1) lines++;
            else if (this.edgeStates[idx] === -1) crosses++;
            else undecided.push(idx);
          }
          
          if (lines > clue || crosses > (4 - clue)) {
            return false; // Contradiction
          }
          
          if (undecided.length > 0) {
            if (lines === clue) {
              for (const idx of undecided) {
                if (!this.setEdgeState(idx, -1)) return false;
              }
            } else if (crosses === 4 - clue) {
              for (const idx of undecided) {
                if (!this.setEdgeState(idx, 1)) return false;
              }
            }
          }


        }
      }
      
      const dotIdx = this.dequeueDot();
      if (dotIdx !== -1) {
        const r = Math.floor(dotIdx / (this.cols + 1));
        const c = dotIdx % (this.cols + 1);
        const dotEdges = this.getDotEdges(r, c);
        
        let lines = 0;
        let crosses = 0;
        const undecided = [];
        
        for (const idx of dotEdges) {
          if (this.edgeStates[idx] === 1) lines++;
          else if (this.edgeStates[idx] === -1) crosses++;
          else undecided.push(idx);
        }
        
        if (lines > 2) {
          return false; // Contradiction
        }
        
        if (undecided.length > 0) {
          if (lines === 2) {
            for (const idx of undecided) {
              if (!this.setEdgeState(idx, -1)) return false;
            }
          } else if (lines === 1 && undecided.length === 1) {
            if (!this.setEdgeState(undecided[0], 1)) return false;
          } else if (lines === 0 && undecided.length === 1) {
            if (!this.setEdgeState(undecided[0], -1)) return false;
          } else if (lines === 0 && undecided.length === 2) {
            // Rule A: Generalized Corner Heuristic
            const e1 = undecided[0];
            const e2 = undecided[1];
            const e1IsH = (e1 < this.numH);
            const e2IsH = (e2 < this.numH);
            if (e1IsH !== e2IsH) {
              const hEdge = e1IsH ? e1 : e2;
              const vEdge = e1IsH ? e2 : e1;
              const hr = Math.floor(hEdge / this.cols);
              const hc = hEdge % this.cols;
              const vr = Math.floor((vEdge - this.numH) / (this.cols + 1));
              const vc = (vEdge - this.numH) % (this.cols + 1);
              
              let cr = -1, cc = -1;
              if (hc === c && vr === r) {
                cr = r; cc = c;
              } else if (hc === c - 1 && vr === r) {
                cr = r; cc = c - 1;
              } else if (hc === c && vr === r - 1) {
                cr = r - 1; cc = c;
              } else if (hc === c - 1 && vr === r - 1) {
                cr = r - 1; cc = c - 1;
              }
              
              if (cr >= 0 && cr < this.rows && cc >= 0 && cc < this.cols) {
                const clue = this.clues[cr][cc];
                if (clue === 3) {
                  if (!this.setEdgeState(e1, 1)) return false;
                  if (!this.setEdgeState(e2, 1)) return false;
                } else if (clue === 1) {
                  if (!this.setEdgeState(e1, -1)) return false;
                  if (!this.setEdgeState(e2, -1)) return false;
                }
              }
            }
          }
        } else {
          if (lines !== 0 && lines !== 2) {
            return false; // Contradiction
          }
        }
      }
    }
    
    return true;
  }

  // Trace drawn lines and check if any closed loop is formed.
  // If a closed loop is formed, but there are other lines elsewhere, or if there are cells with clues
  // that are not yet satisfied (and some edges are still undecided), it is a contradiction.
  // Returns false if a premature loop is detected, true otherwise.
  preventsPrematureLoops() {
    const adj = Array.from({ length: this.numDots }, () => []);
    let totalDrawn = 0;
    
    // Build adjacency list for dots from currently drawn lines (state === 1)
    for (let r = 0; r <= this.rows; r++) {
      for (let c = 0; c <= this.cols; c++) {
        const dotId = r * (this.cols + 1) + c;
        
        // Check horizontal right edge
        if (c < this.cols) {
          const hIdx = r * this.cols + c;
          if (this.edgeStates[hIdx] === 1) {
            const neighborId = dotId + 1;
            adj[dotId].push(neighborId);
            adj[neighborId].push(dotId);
            totalDrawn++;
          }
        }
        
        // Check vertical down edge
        if (r < this.rows) {
          const vIdx = this.numH + r * (this.cols + 1) + c;
          if (this.edgeStates[vIdx] === 1) {
            const neighborId = dotId + (this.cols + 1);
            adj[dotId].push(neighborId);
            adj[neighborId].push(dotId);
            totalDrawn++;
          }
        }
      }
    }
    
    // Divide totalDrawn by 2 since we counted each edge twice
    totalDrawn = totalDrawn / 2;
    if (totalDrawn === 0) return true;
    
    const visited = new Set();
    const loops = [];
    
    for (let i = 0; i < this.numDots; i++) {
      if (adj[i].length > 0 && !visited.has(i)) {
        // Trace this component
        const component = [];
        let curr = i;
        let prev = -1;
        let isLoop = true;
        
        // Basic cycle tracer for degree-2 paths
        while (true) {
          visited.add(curr);
          component.push(curr);
          
          // Find next neighbor
          const nexts = adj[curr].filter(n => n !== prev);
          if (nexts.length === 0) {
            isLoop = false; // Dead end (path, not loop)
            break;
          }
          
          const next = nexts[0];
          if (visited.has(next)) {
            // Loop detected! Check if it connects back to the start of component
            if (next !== component[0]) {
              // A branch or weird shape, shouldn't happen if degree <= 2
              isLoop = false;
            }
            break;
          }
          
          prev = curr;
          curr = next;
        }
        
        if (isLoop && component.length > 2) {
          loops.push(component);
        }
      }
    }
    
    if (loops.length > 0) {
      // We found at least one closed loop.
      // Is there any other drawn edge outside this loop?
      const loopDotCount = loops.reduce((sum, loop) => sum + loop.length, 0);
      
      // If there are other drawn edges outside the loop(s), or if we have multiple separate loops:
      if (loops.length > 1 || loopDotCount < visited.size) {
        return false; // Contradiction: Multiple loops or disjoint paths exist
      }
      
      // If we have exactly one loop, does it contain ALL drawn edges?
      // (loopDotCount === visited.size means yes)
      // If there are still undecided edges in the grid, but we already closed the loop:
      // Check if all clues are fully satisfied. If not, closing the loop now is a contradiction
      // because we can't add any more edges (adding edges would violate degree-2 or create new paths).
      // Allow normal exploration to proceed to leaf nodes where isSolved() strictly validates the complete grid.
    }
    
    return true;
  }

  // Check if current state is a complete and valid solution
  isSolved(strict = false) {
    if (strict) {
      for (let i = 0; i < this.numEdges; i++) {
        if (this.edgeStates[i] === 0) return false;
      }
    }

    // 1. All clues must be satisfied
    for (let r = 0; r < this.rows; r++) {
      for (let c = 0; c < this.cols; c++) {
        const clue = this.clues[r][c];
        if (clue === null) continue;
        
        const cellEdges = this.getCellEdges(r, c);
        const lines = cellEdges.reduce((sum, idx) => sum + (this.edgeStates[idx] === 1 ? 1 : 0), 0);
        if (lines !== clue) return false;
      }
    }

    // 2. Dots must have degree 0 or 2, and there must be at least one loop
    const adj = Array.from({ length: this.numDots }, () => []);
    let edgeCount = 0;
    
    for (let r = 0; r <= this.rows; r++) {
      for (let c = 0; c <= this.cols; c++) {
        const dotId = r * (this.cols + 1) + c;
        
        // Check horizontal right edge
        if (c < this.cols) {
          const hIdx = r * this.cols + c;
          if (this.edgeStates[hIdx] === 1) {
            const neighbor = dotId + 1;
            adj[dotId].push(neighbor);
            adj[neighbor].push(dotId);
            edgeCount++;
          }
        }
        
        // Check vertical down edge
        if (r < this.rows) {
          const vIdx = this.numH + r * (this.cols + 1) + c;
          if (this.edgeStates[vIdx] === 1) {
            const neighbor = dotId + (this.cols + 1);
            adj[dotId].push(neighbor);
            adj[neighbor].push(dotId);
            edgeCount++;
          }
        }
      }
    }

    if (edgeCount === 0) return false; // Loop must have some lines

    // 3. Verify it is a single connected loop
    let startDot = -1;
    for (let i = 0; i < this.numDots; i++) {
      const deg = adj[i].length;
      if (deg !== 0 && deg !== 2) return false; // Any other degree is invalid
      if (deg === 2 && startDot === -1) {
        startDot = i;
      }
    }

    if (startDot === -1) return false;

    // Traverse the loop and count visited dots
    const visited = new Set();
    let curr = startDot;
    let prev = -1;
    
    while (true) {
      visited.add(curr);
      const nexts = adj[curr].filter(n => n !== prev);
      if (nexts.length === 0) return false; // Broken loop
      const next = nexts[0];
      if (visited.has(next)) {
        if (next === startDot) break;
        return false; // Self-intersection
      }
      prev = curr;
      curr = next;
    }

    // Number of visited vertices in the loop should equal the number of vertices with degree 2
    let activeDots = 0;
    for (let i = 0; i < this.numDots; i++) {
      if (adj[i].length === 2) activeDots++;
    }

    return visited.size === activeDots;
  }

  // Solves the puzzle using backtracking with DSU cycle check and AC-3 constraint propagation
  solve(findSingle = false, maxSteps = Infinity) {
    let solutions = [];
    let steps = 0;
    let isTimeout = false;
    
    this.dsuInitFromCurrent();
    
    const backtrack = (depth = 0) => {
      steps++;
      if (steps > maxSteps) {
        isTimeout = true;
        solutions.push("timeout");
        return;
      }
      
      if (depth >= this.maxBackupDepth) {
        return;
      }
      
      // Save global edge states, DSU history
      const backup = this.backupStack[depth];
      backup.set(this.edgeStates);
      const dsuCheckpoint = this.dsuHistory.length;
      
      // Run logical deduction rules: full pass at depth 0, incremental pass at depth > 0
      if (depth === 0) {
        if (!this.deduct()) {
          this.edgeStates.set(backup);
          this.clearQueues();
          this.dsuRollback(dsuCheckpoint);
          return;
        }
      } else {
        if (!this.deductIncremental()) {
          this.edgeStates.set(backup);
          this.clearQueues();
          this.dsuRollback(dsuCheckpoint);
          return;
        }
      }
      
      const undecidedIdx = this.edgeStates.indexOf(0);
      if (undecidedIdx === -1) {
        if (this.isSolved(true)) {
          const sol = new Int8Array(this.edgeStates);
          solutions.push(sol);
        }
        this.edgeStates.set(backup);
        this.clearQueues();
        this.dsuRollback(dsuCheckpoint);
        return;
      }
      
      if (solutions.length >= 2 || (findSingle && solutions.length >= 1) || isTimeout) {
        this.edgeStates.set(backup);
        this.clearQueues();
        this.dsuRollback(dsuCheckpoint);
        return;
      }
      
      // Save state AFTER deduction
      const backupAfterDeduct = this.backupAfterDeductStack[depth];
      backupAfterDeduct.set(this.edgeStates);
      const dsuCheckpointAfterDeduct = this.dsuHistory.length;
      
      // Branching heuristic: find clue cell with minimum undecided edges (MRV)
      let branchIdx = -1;
      let minUndecided = 999;
      
      for (let r = 0; r < this.rows; r++) {
        for (let c = 0; c < this.cols; c++) {
          const clue = this.clues[r][c];
          if (clue !== null) {
            const cellEdges = this.getCellEdges(r, c);
            let undecidedCount = 0;
            let firstUndecided = -1;
            
            for (let j = 0; j < 4; j++) {
              if (this.edgeStates[cellEdges[j]] === 0) {
                undecidedCount++;
                if (firstUndecided === -1) {
                  firstUndecided = cellEdges[j];
                }
              }
            }
            
            if (undecidedCount > 0 && undecidedCount < minUndecided) {
              minUndecided = undecidedCount;
              branchIdx = firstUndecided;
              if (minUndecided === 1) {
                break;
              }
            }
          }
        }
        if (minUndecided === 1) {
          break;
        }
      }
      
      if (branchIdx === -1) {
        branchIdx = undecidedIdx; // Fallback
      }
      
      // Try setting edge to 1 (line)
      if (this.setEdgeState(branchIdx, 1)) {
        backtrack(depth + 1);
      }
      this.dsuRollback(dsuCheckpointAfterDeduct);
      this.edgeStates.set(backupAfterDeduct);
      this.clearQueues();
      
      if (solutions.length >= 2 || (findSingle && solutions.length >= 1) || isTimeout) {
        this.dsuRollback(dsuCheckpoint);
        this.edgeStates.set(backup);
        this.clearQueues();
        return;
      }
      
      // Try setting edge to -1 (cross)
      if (this.setEdgeState(branchIdx, -1)) {
        backtrack(depth + 1);
      }
      this.dsuRollback(dsuCheckpointAfterDeduct);
      this.edgeStates.set(backupAfterDeduct);
      this.clearQueues();
      
      // Cleanup to restore parent state
      this.dsuRollback(dsuCheckpoint);
      this.edgeStates.set(backup);
      this.clearQueues();
    };
    
    backtrack(0);
    return solutions;
  }
}

// Bind to global scope for Web Worker and local compatibility
if (typeof self !== 'undefined') {
  self.LoopCourseSolver = LoopCourseSolver;
} else if (typeof window !== 'undefined') {
  window.LoopCourseSolver = LoopCourseSolver;
} else {
  globalThis.LoopCourseSolver = LoopCourseSolver;
}

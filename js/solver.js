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
    
    this.edgeStates = new Array(this.numEdges).fill(0); // 0 = empty, 1 = line, -1 = cross
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
    return [
      this.getHEdgeIndex(r, c),     // Top
      this.getVEdgeIndex(r, c + 1), // Right
      this.getHEdgeIndex(r + 1, c), // Bottom
      this.getVEdgeIndex(r, c)      // Left
    ];
  }

  // Returns array of up to 4 edge indices connected to dot (r, c)
  getDotEdges(r, c) {
    const edges = [];
    const up = this.getVEdgeIndex(r - 1, c);
    const down = this.getVEdgeIndex(r, c);
    const left = this.getHEdgeIndex(r, c - 1);
    const right = this.getHEdgeIndex(r, c);
    
    if (up !== -1) edges.push(up);
    if (down !== -1) edges.push(down);
    if (left !== -1) edges.push(left);
    if (right !== -1) edges.push(right);
    return edges;
  }

  // Run logical deduction rules repeatedly until no more progress is made
  // Returns false if a contradiction is found, true otherwise
  deduct() {
    let changed = true;
    while (changed) {
      changed = false;
      
      // 1. Cell clue deductions
      for (let r = 0; r < this.rows; r++) {
        for (let c = 0; c < this.cols; c++) {
          const clue = this.clues[r][c];
          if (clue === null) continue;
          
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
              // Remaining must be crosses
              for (const idx of undecided) {
                this.edgeStates[idx] = -1;
                changed = true;
              }
            } else if (crosses === 4 - clue) {
              // Remaining must be lines
              for (const idx of undecided) {
                this.edgeStates[idx] = 1;
                changed = true;
              }
            }
          }
        }
      }
      
      // 2. Dot degree deductions
      for (let r = 0; r <= this.rows; r++) {
        for (let c = 0; c <= this.cols; c++) {
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
            return false; // Contradiction: degree cannot exceed 2
          }
          
          if (undecided.length > 0) {
            if (lines === 2) {
              // Degree is already 2, rest must be crosses
              for (const idx of undecided) {
                this.edgeStates[idx] = -1;
                changed = true;
              }
            } else if (lines === 1 && undecided.length === 1) {
              // Degree is 1 and only 1 undecided remains: it must be a line
              const idx = undecided[0];
              this.edgeStates[idx] = 1;
              changed = true;
            } else if (lines === 0 && undecided.length === 1) {
              // A dot cannot have degree 1. If 0 lines, and only 1 edge is undecided,
              // it cannot be 1 (that would make degree 1), so it must be -1.
              const idx = undecided[0];
              this.edgeStates[idx] = -1;
              changed = true;
            }
          } else {
            // No undecided edges
            if (lines !== 0 && lines !== 2) {
              return false; // Contradiction: degree must be 0 or 2
            }
          }
        }
      }
      
      // 3. Early dead-end and small-loop prevention
      // If we close a loop, it must contain ALL drawn edges.
      // If there are multiple separate drawn paths, they shouldn't close prematurely.
      if (this.preventsPrematureLoops() === false) {
        return false;
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
        const hIdx = this.getHEdgeIndex(r, c);
        if (hIdx !== -1 && this.edgeStates[hIdx] === 1) {
          const neighborId = r * (this.cols + 1) + (c + 1);
          adj[dotId].push(neighborId);
          adj[neighborId].push(dotId);
          totalDrawn++;
        }
        
        // Check vertical down edge
        const vIdx = this.getVEdgeIndex(r, c);
        if (vIdx !== -1 && this.edgeStates[vIdx] === 1) {
          const neighborId = (r + 1) * (this.cols + 1) + c;
          adj[dotId].push(neighborId);
          adj[neighborId].push(dotId);
          totalDrawn++;
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
      let hasUndecided = this.edgeStates.some(s => s === 0);
      if (hasUndecided) {
        // Check if there are clues that are not satisfied
        for (let r = 0; r < this.rows; r++) {
          for (let c = 0; c < this.cols; c++) {
            const clue = this.clues[r][c];
            if (clue === null) continue;
            
            const cellEdges = this.getCellEdges(r, c);
            const lines = cellEdges.reduce((sum, idx) => sum + (this.edgeStates[idx] === 1 ? 1 : 0), 0);
            if (lines !== clue) {
              return false; // Contradiction: loop is closed but clues are not satisfied
            }
          }
        }
        
        // Loop is closed and all clues are satisfied, but we still have undecided edges.
        // In Loop Course, we can just cross out all remaining undecided edges!
        for (let i = 0; i < this.numEdges; i++) {
          if (this.edgeStates[i] === 0) {
            this.edgeStates[i] = -1;
          }
        }
      }
    }
    
    return true;
  }

  // Check if current state is a complete and valid solution
  isSolved() {
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
        const hIdx = this.getHEdgeIndex(r, c);
        if (hIdx !== -1 && this.edgeStates[hIdx] === 1) {
          const neighbor = r * (this.cols + 1) + (c + 1);
          adj[dotId].push(neighbor);
          adj[neighbor].push(dotId);
          edgeCount++;
        }
        const vIdx = this.getVEdgeIndex(r, c);
        if (vIdx !== -1 && this.edgeStates[vIdx] === 1) {
          const neighbor = (r + 1) * (this.cols + 1) + c;
          adj[dotId].push(neighbor);
          adj[neighbor].push(dotId);
          edgeCount++;
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

  // Solves the puzzle using backtracking.
  // Returns number of solutions found: 0, 1, or 2 (stops early if a second is found to speed up uniqueness check).
  // If `findSingle` is true, it stops immediately after finding the first solution.
  solve(findSingle = false) {
    let solutions = [];
    
    const backtrack = () => {
      // 1. Run deduction rules
      const backup = [...this.edgeStates];
      if (!this.deduct()) {
        this.edgeStates = backup;
        return; // Contradiction found, backtrack
      }
      
      // 2. Check if solved
      if (this.isSolved()) {
        solutions.push([...this.edgeStates]);
        this.edgeStates = backup;
        return;
      }
      
      // If all edges are decided but not a valid solution, backtrack
      const undecidedIdx = this.edgeStates.indexOf(0);
      if (undecidedIdx === -1) {
        this.edgeStates = backup;
        return;
      }
      
      // Stop search if we already found enough solutions
      if (solutions.length >= 2 || (findSingle && solutions.length >= 1)) {
        this.edgeStates = backup;
        return;
      }
      
      // 3. Choose an undecided edge to branch on
      // Heuristic: choose an edge that is around a cell with a clue to constrain faster
      let branchIdx = undecidedIdx;
      
      // Find an undecided edge adjacent to a clue cell
      outer: for (let r = 0; r < this.rows; r++) {
        for (let c = 0; c < this.cols; c++) {
          if (this.clues[r][c] !== null) {
            const cellEdges = this.getCellEdges(r, c);
            for (const idx of cellEdges) {
              if (this.edgeStates[idx] === 0) {
                branchIdx = idx;
                break outer;
              }
            }
          }
        }
      }
      
      // Try setting edge to 1 (line)
      this.edgeStates[branchIdx] = 1;
      backtrack();
      
      if (solutions.length >= 2 || (findSingle && solutions.length >= 1)) {
        this.edgeStates = backup;
        return;
      }
      
      // Try setting edge to -1 (cross)
      this.edgeStates[branchIdx] = -1;
      backtrack();
      
      // Restore state
      this.edgeStates = backup;
    };
    
    backtrack();
    return solutions;
  }
}

// Bind to window for local file protocol compatibility without modules
window.LoopCourseSolver = LoopCourseSolver;

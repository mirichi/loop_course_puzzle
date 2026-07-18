const fs = require('fs');
const path = require('path');
const createLoopCourseModule = require('./js/loopcourse.js');

async function main() {
    const args = process.argv.slice(2);
    if (args.length < 3) {
        console.error("Usage: node export_pencilbox_step.js <path_to_puzzle.txt> <path_to_deduction.csv> <step>");
        process.exit(1);
    }

    const puzzleFile = args[0];
    const csvFile = args[1];
    const targetStep = parseInt(args[2], 10);

    const puzzleText = fs.readFileSync(puzzleFile, 'utf8').trim();
    const puzzleLines = puzzleText.split(/\r?\n/).map(l => l.trim()).filter(l => l.length > 0);
    const rows = parseInt(puzzleLines[0], 10);
    const cols = parseInt(puzzleLines[1], 10);

    // Read clues
    const parsedClues = new Int8Array(rows * cols);
    parsedClues.fill(-1);
    let cellIdx = 0;
    for (let i = 2; i < 2 + rows; i++) {
        if (!puzzleLines[i]) break;
        const tokens = puzzleLines[i].split(/\s+/);
        for (let j = 0; j < cols; j++) {
            if (tokens[j] !== undefined && tokens[j] !== '.') {
                parsedClues[cellIdx] = parseInt(tokens[j], 10);
            }
            cellIdx++;
        }
    }

    // Run WASM to get solved states
    const Module = await createLoopCourseModule();
    const init_grid = Module.cwrap('init_grid', null, ['number', 'number']);
    const get_clues_ptr = Module.cwrap('get_clues_ptr', 'number', []);
    const set_advanced_ac3 = Module.cwrap('set_advanced_ac3', null, ['number']);
    const analyze_puzzle = Module.cwrap('analyze_puzzle', null, []);
    const solve_puzzle_wasm = Module.cwrap('solve_puzzle_wasm', 'number', ['boolean', 'number']);
    const get_solution_ptr = Module.cwrap('get_solution_ptr', 'number', ['number']);
    const get_edge_states_ptr = Module.cwrap('get_edge_states_ptr', 'number', []);

    init_grid(rows, cols);
    set_advanced_ac3(1);
    
    const cluesPtr = get_clues_ptr();
    for (let i = 0; i < rows * cols; i++) {
        Module.HEAP8[cluesPtr + i] = parsedClues[i];
    }
    
    // Solve first to get correct solution from clean state
    const edgesPtrForClean = get_edge_states_ptr();
    const numEdges = (rows + 1) * cols + rows * (cols + 1);
    const wasmEdgeData = new Int8Array(Module.HEAP8.buffer, edgesPtrForClean, numEdges);
    wasmEdgeData.fill(0);
    
    const solveCount = solve_puzzle_wasm(true, 1000000);
    console.log(`solve_puzzle_wasm returned solutions: ${solveCount}`);
    
    const edgesPtr = get_solution_ptr(0);
    const solvedEdgeStates = new Int8Array(Module.HEAP8.slice(edgesPtr, edgesPtr + numEdges));
    
    // Now run analysis
    wasmEdgeData.fill(0);
    analyze_puzzle();

    // Read CSV to find which edges were set
    const newEdgeStates = new Int8Array(numEdges);
    newEdgeStates.fill(0);
    
    const csvText = fs.readFileSync(csvFile, 'utf8').trim();
    const csvLines = csvText.split(/\r?\n/);
    
    let appliedSteps = 0;
    for (let i = 0; i < csvLines.length; i++) {
        const line = csvLines[i].trim();
        if (!line) continue;
        const parts = line.split(',');
        const step = parseInt(parts[0], 10);
        if (isNaN(step)) continue; // Skip header
        const edgeIdx = parseInt(parts[1], 10);
        
        if (step > targetStep) break;
        
        if (edgeIdx >= 0 && edgeIdx < numEdges) {
            newEdgeStates[edgeIdx] = solvedEdgeStates[edgeIdx];
        }
        appliedSteps++;
    }
    
    console.log(`Applied ${appliedSteps} steps.`);

    // Output to file
    const outName = `${path.basename(puzzleFile, path.extname(puzzleFile))}_step${targetStep}.txt`;
    let out = `${rows}\n${cols}\n`;
    
    // clues
    for (let r = 0; r < rows; r++) {
        let rowStrs = [];
        for (let c = 0; c < cols; c++) {
            let val = parsedClues[r * cols + c];
            rowStrs.push(val === -1 ? '.' : val.toString());
        }
        out += rowStrs.join(' ') + '\n';
    }
    
    // horizontal edges
    let hIdx = 0;
    for (let r = 0; r <= rows; r++) {
        let rowStrs = [];
        for (let c = 0; c < cols; c++) {
            rowStrs.push(newEdgeStates[hIdx++].toString());
        }
        out += rowStrs.join(' ') + '\n';
    }
    
    // vertical edges
    let vIdx = (rows + 1) * cols;
    for (let r = 0; r < rows; r++) {
        let rowStrs = [];
        for (let c = 0; c <= cols; c++) {
            rowStrs.push(newEdgeStates[vIdx++].toString());
        }
        out += rowStrs.join(' ') + '\n';
    }
    
    fs.writeFileSync(outName, out);
    console.log(`Wrote ${outName}`);
}

main().catch(console.error);

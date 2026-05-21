# DualGrounder
Incremental ASP solving problem leveraging Clingo's API to lazily and incrementally ground programs.
Created by the Knowledge Representation and Natural Language Processing Lab at the University of Nebraska at Omaha by Justin Robbins and Yuliya Lierler.

## Files
	__pycache__ - Cache for the executable
	build - Libraries for the executable
	dist - Contains the executable file; this is where you run dualgrounder
	dualgrounder.py - Original python code of the executable
	dualgrounder.spec - Spec file for the executable
	benchmark - Contains the benchmark encodings and instances used to test DualGrounder

## Python File Installation Requirements
Python Packages:
- Python 3.7+
- Clingo 5.5+

The dualgrounder executable can be run using the following command in the /dist folder:

		dualgrounder encoding-file instance-file lazy-file --splitprog

**Note on Clingo versions:** This version has been ported to the Clingo 5.5+ API. The original code depended on `clingo_ast_util` and used `clingo.parse_program`, both of which were removed in Clingo 5.5. The current version uses `clingo.ast.parse_string`/`clingo.ast.parse_files` and `ProgramBuilder`, with the `clingo_ast_util` helpers inlined directly. Input files with `#include` directives are now resolved correctly via `parse_files`. Anonymous variables (`_`) in constraints are also now supported.

## Arguments
	encoding-file - File containing the ASP rules of the problem encoding not in the lazy-file
	instance-file - File containing the ASP rules of the problem instance
	lazy-file - File containing the ASP rules to be instantiated lazily

By default, dualgrounder will separate all constraints from the given files and lazily ground them. 
The rules may also simply be in one file; dualgrounder appends all of the input files into a single program aside from the
constraints to be lazily instantiated. The --splitprog command ensure that only the rules in lazy-file are lazily grounded.

These arguments can be used to customize dualgrounder's behavior:

**--debugprint**: Activates various print statement to provide detailed feedback about daulgrounder's execution.

**--wasplike**: Instructs dualgrounder to utilize solving heuristics to cause the Clingo solver to try and emulate Wasp heuristics.
	
**--splitprog**: Causes only the last input file given to be lazily grounded. This file must consist entirely of constraints. Constraints in the other input files will not be lazily grounded.

**--iterlim=int**: Takes in an integer value that limits the number of ground-solve iterations dualgrounder will execute.

## Benchmarks
- NLP/NLU
- Packing
- StableMarriage
		
Typically, these are ran by giving dualgrounder.py the *-nc encoding with an instance, along with the lazy-* file as the last file argument with the --splitprog command.
For example:
			
StableMarriage example command:
			
	python dualgrounder.py ../benchmarks/StableMarriage/encodings/SM-nc/encoding-nc.asp ../benchmarks/StableMarriage/instances/stablemarriage_0-perc_inst-1 ../benchmarks/StableMarriage/lazy-SM.asp --splitprog 

## License
	DualGrounder is distibuted under the MIT license
			
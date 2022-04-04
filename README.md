# Scheme Compiler

## About The Project

I developed this compiler alone in my "Compilation Principles" course.

In the first iteration I implemented the Reader that basically parsed the scheme code to the S-expression notation.

In the second iteration I implemented the Tag Parser. The main goal was to convert the S-expression into an expression.

In the third iteration I implemented the Semantic Analyser. In this iteration I converted the expression into an expression'. I found which variables needed to be boxed and which variables were in the tail position.

In the final iteration I implemented the Code Generator. Here I converted the expression' into assembly code. In addition, I implemented the TCO (Tail Call Optimization) and the boxing mechanism.

## Usage

Follow these steps in order to run the project:
1. Download all of the files.
2. Open the 'example.scm' file in a text editor and write your Chez Scheme code there.
3. Open the Terminal and navigate to the project's directory.
4. Run the following command (This compiles the file): tests/test_compiler1.sh example
5. Run the following command (This runs the file): ./example
6. The output of the file will appear in your terminal.
7. In order to run something else, manually delete the example, example.o and example.s files, and go to step 2.


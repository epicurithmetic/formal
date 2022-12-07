# Turing Machine ASCII Visualisation

This repository has code to generate ASCII visualisations of computations performed by a Turing machine. 

## Example :abacus:

During the process of computing 1101<sub>2</sub> + 1<sub>2</sub> the Turing machine reaches the following state.

                              ||---|---|---|---|---|---|---|---|---|---|---|---|---|
                              || @ | 1 | 1 | 0 |   | + |   | c | 1 | s | 0 |   |   |
                              ||---|---|---|---|---|---|---|---|---|---|---|---|---|
                                                        | |  
                                                       /   \
                                                      |C: q4|
                                                      |P: b |
                                                      |M: L |
                                                      |U: q4|
                                                      -------
This Turing machine uses the special characters 'c' and 's' to keep track of the carry and sum. 
It prints the sum in reverse at the end of the tape. Once the machine has finished it moves the sum back to the start of the tape, then halts.

An example of an entire computation can be seen in the .gif below. Each bit is summed, the carry is stored in memory. Finally the sum is moved to the beginning of the tape.

<p align="center">
  <img width="420" height="100" src="https://github.com/epicurithmetic/turingMachine/blob/master/images/binary-sum.gif">
</p>

## How to use this script

To perform a calculation you will need: 
  1. Input tape ([Example: Input for binary sum](https://github.com/epicurithmetic/turingMachine/blob/master/tm-tape.txt))
  2. Turing machine instructions ([Example: Sum of two binary numbers](https://github.com/epicurithmetic/turingMachine/blob/master/tm-code-binaryaddition.txt))
  3. Run [tmMain.py](https://github.com/epicurithmetic/turingMachine/blob/master/tmMain.py) with these as input files. 

The script generates a .txt file with each step of the computation recorded.

### Syntax 
  
  Input tape is assumed to be (in theory) infinite to the right, the start (left) of the tape is indicated using an (@) symbol.
  Further cells are specified by characters separated by commas. Note that lowercase 'b' is a special character used to denote a blank cell. 
  Any cell not specified at the start of the computation is assumed blank.
  
  Instruction files are .txt files for which each line is either (i) an instruction, or (ii) a comment. Comment lines are denoted by an #
  An example of a section of some instructions are displayed below.

                                                q0,b,c,R,q1;
                                                q1,b,0,R,q2;
                                                q2,b,s,L,q3;
                                                # This is a comment line
                                                q3,0,0,L,q3;
                                                q3,1,1,L,q3;
                                                q3,s,s,L,q3;

The five parts of an instruction are to be read: in the current state (q0), reading the current symbol (b), the machine will write this symbol (c), move one cell in this direction (R), and update into this state (q1).
Note the semi-colon ; to end each instruction. Furthermore the final line of the instructions needs to end with a new-line character. Move instructions can be one of either (L)eft, (N)owhere, or (R)ight.

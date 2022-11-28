from tmCode import turingMachine

# Write the name of the machine code file here.
tm_code = "test.txt"

# Write the name of the input tape file here.
tm_tape = "tm-tape.txt"

# This line intialises the Turing Machine with code and tape.
tm = turingMachine(tm_code,tm_tape)

# This line does the computation and writes the output to a text file.
tm.execute_computation()
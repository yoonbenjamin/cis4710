        .section .data
input_string:   .asciz "Hello world!"

        # tohost/fromhost are data locations used by Spike
        .align 8
tohost: .byte 0
        .align 8
fromhost: .byte 0

        
        .section .text
        .globl _start
_start:
        # Load the address of the input string into a0
        la a0, input_string

        # Your code here!

        # Loop over each character
        main_loop:
                # Load 8-bit value from a0 to a1
                lb a1, 0(a0)

                # Check to see if the string has ended
                sub a2, a2, a2  
                beq a1, a2, end_program  # Branch to the end of the program if string ended

                # Copy a1 to a4 before modifying it
                mv a4, a1

                # Check if this a letter and if it's lowercase
                li a3, 97  # Load ASCII value for 'a'
                blt a1, a3, no_conversion  # Branch if no coversion is necessary (not a lowercase letter)
                li a3, 123  # Load ASCII value for 'z' + 1
                bge a1, a3, no_conversion  # Branch if no conversion is necessary (not a lowercase letter)

                # Convert to uppercase letter
                addi a1, a4, -32

        no_conversion:
                # Store letter in a1 register
                sb a1, 0(a0)
                addi a0, a0, 1
                j main_loop  # Continue looping over characters
        
end_program:
        # jump here when you're done
        j end_program


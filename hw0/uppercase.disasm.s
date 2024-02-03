
uppercase.bin:     file format elf32-littleriscv


Disassembly of section .text:

00010074 <_start>:
   10074:	ffff2517          	auipc	a0,0xffff2
   10078:	f8c50513          	addi	a0,a0,-116 # 2000 <__DATA_BEGIN__>

0001007c <main_loop>:
   1007c:	00050583          	lb	a1,0(a0)
   10080:	40c60633          	sub	a2,a2,a2
   10084:	02c58463          	beq	a1,a2,100ac <end_program>
   10088:	00058713          	mv	a4,a1
   1008c:	06100693          	li	a3,97
   10090:	00d5c863          	blt	a1,a3,100a0 <no_conversion>
   10094:	07b00693          	li	a3,123
   10098:	00d5d463          	bge	a1,a3,100a0 <no_conversion>
   1009c:	fe070593          	addi	a1,a4,-32

000100a0 <no_conversion>:
   100a0:	00b50023          	sb	a1,0(a0)
   100a4:	00150513          	addi	a0,a0,1
   100a8:	fd5ff06f          	j	1007c <main_loop>

000100ac <end_program>:
   100ac:	0000006f          	j	100ac <end_program>

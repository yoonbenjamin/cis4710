
uppercase.bin:     file format elf32-littleriscv


Disassembly of section .text:

00010074 <_start>:
   10074:	ffff2517          	auipc	a0,0xffff2
   10078:	f8c50513          	addi	a0,a0,-116 # 2000 <__DATA_BEGIN__>

0001007c <main_loop>:
   1007c:	00050583          	lb	a1,0(a0)
   10080:	40c60633          	sub	a2,a2,a2
   10084:	02c58263          	beq	a1,a2,100a8 <end_program>
   10088:	06100693          	li	a3,97
   1008c:	00d5c863          	blt	a1,a3,1009c <no_conversion>
   10090:	07b00693          	li	a3,123
   10094:	00d5d463          	bge	a1,a3,1009c <no_conversion>
   10098:	fe058593          	addi	a1,a1,-32

0001009c <no_conversion>:
   1009c:	00b50023          	sb	a1,0(a0)
   100a0:	00150513          	addi	a0,a0,1
   100a4:	fd9ff06f          	j	1007c <main_loop>

000100a8 <end_program>:
   100a8:	0000006f          	j	100a8 <end_program>

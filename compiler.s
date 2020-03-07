%define T_UNDEFINED 0
%define T_VOID 1
%define T_NIL 2
%define T_INTEGER 3
%define T_FLOAT 4
%define T_BOOL 5
%define T_CHAR 6
%define T_STRING 7
%define T_SYMBOL 8
%define T_CLOSURE 9
%define T_PAIR 10
	
%define CHAR_NUL 0
%define CHAR_TAB 9
%define CHAR_NEWLINE 10
%define CHAR_PAGE 12
%define CHAR_RETURN 13
%define CHAR_SPACE 32
%define CHAR_DOUBLEQUOTE 34
%define CHAR_BACKSLASH 92
	
%define TYPE_SIZE 1
%define WORD_SIZE 8


	
%define KB(n) n*1024
%define MB(n) 1024*KB(n)
%define GB(n) 1024*MB(n)



%macro SKIP_TYPE_TAG 2
	mov %1, qword [%2+TYPE_SIZE]	
%endmacro	

%define INT_VAL SKIP_TYPE_TAG

%macro CHAR_VAL 2
	movzx %1, byte [%2+TYPE_SIZE]
%endmacro

%define FLOAT_VAL SKIP_TYPE_TAG

%define STRING_LENGTH SKIP_TYPE_TAG

%define SYMBOL_VAL SKIP_TYPE_TAG
%define PARAM_COUNT qword [rbp+3*WORD_SIZE]

%macro PUSH_STACK 0
   push rbp
   mov rbp,rsp
%endmacro

%macro STRING_ELEMENTS 2
	lea %1, [%2+TYPE_SIZE+WORD_SIZE]
%endmacro

%define CAR SKIP_TYPE_TAG

%macro CDR 2
	mov %1, qword [%2+TYPE_SIZE+WORD_SIZE]
%endmacro




%define CLOSURE_ENV CAR

%define CLOSURE_CODE CDR

%define PVAR(n) qword [rbp+(4+n)*WORD_SIZE]
	
%define SOB_UNDEFINED T_UNDEFINED
%define SOB_NIL T_NIL
%define SOB_VOID T_VOID
%define SOB_FALSE word T_BOOL
%define SOB_TRUE word (1 << TYPE_SIZE | T_BOOL)

%macro MOV_INS 3
	mov %1, [%2 + WORD_SIZE * %3]
%endmacro

%define MOV_INSTRUCTION MOV_INS

%macro MOV_QWORD 3
	mov %1, qword[%2 + %3]
%endmacro

%define MOV_INSTRUCTION_QWORD MOV_QWORD

%macro MOV_TWO 3
	mov [%1 + WORD_SIZE * %2], %3
%endmacro

%define MOV_TWO_INS MOV_TWO

%macro MOV_BYTES 3
	mov %1, qword [%2 + WORD_SIZE * %3]
%endmacro

%define MOV_TWO_BYTES MOV_BYTES


%define MOV_TWO_INS MOV_TWO

%macro MOV_BYTES_TWO 3
	mov qword[%1 + WORD_SIZE *%2],  %3
%endmacro

%define MOV_QWORD_TWO MOV_BYTES_TWO

%macro UPDATED_REG 0
	add r9, 4
  	add r9, r9
        add r9, r9
        add r9, r9
        MOV_INSTRUCTION_QWORD r10, rbp, r9
        sub r9, WORD_SIZE
        MOV_INSTRUCTION_QWORD r12, rbp, r9
        MAKE_PAIR(r11, r12, r10)
        sub rcx, 1
        cmp rcx, 0
%endmacro

%define UPDATE_REG UPDATED_REG

%macro LAMBDA_LOOP 3 
 	mov r10, %1
        add r10, r10
        add r10, r10
        add r10, r10
        MALLOC r12, r10
        mov [rbx], r12
        mov rcx, %1
        xor r9, r9
        cmp rcx, 0
        loop_%2_%3:
        jz leave_%2_%3
        mov r10, r9
        add r10, 1
        add r10, 1
        add r10, 1
        add r10, 1
        MOV_TWO_BYTES r11, rbp, r10
        MOV_QWORD_TWO r12, r9, r11
        add r9, 1
        add rcx, -1
        jmp loop_%2_%3
        leave_%2_%3:
%endmacro

%define LAMBDA_LOOPS LAMBDA_LOOP

%macro LAMBDAOPT_LOOP 2
	MAKE_CLOSURE(rax, rbx, closure_%1)
        jmp leave_%1
        closure_%1:
        push rbp
        mov rbp, rsp
        MOV_INSTRUCTION_QWORD r9, rbp, 24
        mov r10, %2
        cmp r10, r9
        je procc_%1
        MOV_INSTRUCTION_QWORD  rcx, rbp, 24
        sub rcx, %2
        UPDATE_REG
        check_%1:
        jz done_%1_iter
        add r9, -8
        MOV_INSTRUCTION_QWORD r12, rbp, r9
        MAKE_PAIR(r10, r12 , r11)
        mov r11, r10
        add rcx, -1
        jmp check_%1
        done_%1_iter:
        mov qword[ rbp + r9], r11
        procc_%1:
        leave
        push rbp
        mov rbp, rsp 
%endmacro
%define LAMBDAOPT_LOOPS LAMBDAOPT_LOOP

%macro DEPTH_ONE 0
	mov r10, 1
        add r10, r10
        add r10, r10
        add r10, r10
        MALLOC rbx, r10
%endmacro	
%define DEPTHS_ONE DEPTH_ONE

%macro FRAME_ONE 3 
	  mov rcx, 0
	  mov r9, 1
          mov r12, %1    
          add r12, r12
          add r12, r12
          add r12, r12
          MALLOC rbx, r12
          MOV_INSTRUCTION_QWORD r10, rbp,16
          loop%2:
          je end_l%2
          MOV_INSTRUCTION r12, r10, rcx 
          MOV_TWO_INS rbx, r9, r12
          add rcx, 1
          add r9, 1
          cmp rcx, %3
          jl loop%2
          end_l%2:
%endmacro
%define FRAME_INS FRAME_ONE

%macro NOT_TAIL 0
 	CLOSURE_CODE rbx, rax
      	call rbx
        add rsp, WORD_SIZE
        pop rbx
        add rbx, rbx
        add rbx, rbx
        add rbx, rbx
        add rsp, rbx
        add rsp, WORD_SIZE
%endmacro
%define NOT_TAIL_POSITION NOT_TAIL


%macro DONE_TASK 0
   leave
   ret
%endmacro 

%macro SHIFT_FRAME 1 
	mov r14, qword[rbp + 24]
	push rax
	mov rax, PARAM_COUNT
	add rax, 5
%assign i 1
%rep %1
	dec rax
	mov r15, qword[rbp - WORD_SIZE* i]
	mov qword[rbp+WORD_SIZE*rax], r15
%assign i i+1
%endrep
	pop rax
	add r14, 5
	add r14, r14
	add r14, r14
	add r14, r14
	add rsp, r14
	
%endmacro

%macro YES_TAIL 1
 	push qword[rbp + WORD_SIZE]
        push qword[rbp]
        SHIFT_FRAME %1
        CLOSURE_CODE rbx, rax
        pop rbp
        jmp rbx
%endmacro
%define YES_TAIL_POSITION YES_TAIL

%macro APPLY_LOOP_R3 1
		mov %1, rcx
	add %1, %1
	add %1, %1
	add %1, %1
	add %1, WORD_SIZE
	add %1, WORD_SIZE
	add %1, WORD_SIZE
	add %1, WORD_SIZE
	push qword[rbp + %1]
%endmacro
%define APPLY_LOOP APPLY_LOOP_R3
%macro APPLY_PUSH_R 1 
	mov r8, rcx
	mov %1, rcx
	add %1, %1
	add %1, %1
	add %1, %1
	sub rsp, %1
	mov r13, rsp
	cmp rcx, 0
%endmacro

%macro CALC_SHIFT_CAR 1
	MOV_TWO_BYTES r14, rbp, 3
	push rax
	MOV_TWO_BYTES rax, rbp, 3
	add rax, WORD_SIZE
	add rax, -3
	mov rbx, -1
	add %1, WORD_SIZE
	add %1, -3
	cmp %1, 0
%endmacro

%define CALC_SHIFT CALC_SHIFT_CAR

%define APPLY_PUSH APPLY_PUSH_R

%macro APPLY_LOOP_CDR 2
	add rcx, 1
	CDR %1, %2
	mov %2, %1
%endmacro

%define APPLY_CDR APPLY_LOOP_CDR

%macro APPLY_LOOP_SECOND 3 
	CAR %1, %2
	mov qword[%3], %1
	add %3, WORD_SIZE
	CDR %1, %2
	mov %2, %1
	add rcx , -1
%endmacro

%define APPLY_LOOP_SEC APPLY_LOOP_SECOND
%macro APPLY_SHIFT_R 3 
	pop %1
	add %2, WORD_SIZE
	add %2, -3
	add %2, %2
	add %2, %2
	add %2, %2
	add %3, %2
%endmacro
%define APPLY_SHIFT APPLY_SHIFT_R

%macro APPLY_DONE 2 
	add %2, %1
	mov %1, %2
	push %2
	MOV_INSTRUCTION %2, rbp, 4
	push qword[%2 + 1]
	push qword[rbp + WORD_SIZE]
	push qword[rbp]
%endmacro

%define APPLY_MACRO_DONE APPLY_DONE

%macro APPLY_SHIFT_LOOP 1 
	add rax, -1
	MOV_TWO_BYTES %1, rbp, rbx
	MOV_QWORD_TWO rbp, rax, %1
	add rbx, -1
	add r8, -1
%endmacro

%define APPLY_SHIFT_DONE APPLY_SHIFT_LOOP

; returns %2 allocated bytes in register %1
; Supports using with %1 = %2
%macro MALLOC 2
	add qword [malloc_pointer], %2
	push %2
	mov %1, qword [malloc_pointer]
	sub %1, [rsp]
	add rsp, 8
%endmacro
	
; Creates a short SOB with the
; value %2
; Returns the result in register %1
%macro MAKE_CHAR_VALUE 2
	MALLOC %1, 1+TYPE_SIZE
	mov byte [%1], T_CHAR
	mov byte [%1+TYPE_SIZE], %2
%endmacro

; Creates a long SOB with the
; value %2 and type %3.
; Returns the result in register %1
%macro MAKE_LONG_VALUE 3
	MALLOC %1, TYPE_SIZE+WORD_SIZE
	mov byte [%1], %3
	mov qword [%1+TYPE_SIZE], %2
%endmacro

%define MAKE_INT(r,val) MAKE_LONG_VALUE r, val, T_INTEGER
%define MAKE_FLOAT(r,val) MAKE_LONG_VALUE r, val, T_FLOAT
%define MAKE_CHAR(r,val) MAKE_CHAR_VALUE r, val

; Create a string of length %2
; from char %3.
; Stores result in register %1
%macro MAKE_STRING 3
	lea %1, [%2+WORD_SIZE+TYPE_SIZE]
	MALLOC %1, %1
	mov byte [%1], T_STRING
	mov qword [%1+TYPE_SIZE], %2
	push rcx
	add %1,WORD_SIZE+TYPE_SIZE
	mov rcx, %2
	cmp rcx, 0
%%str_loop:
	jz %%str_loop_end
	dec rcx
	mov byte [%1+rcx], %3
	jmp %%str_loop
%%str_loop_end:
	pop rcx
	sub %1, WORD_SIZE+TYPE_SIZE
%endmacro

;Make a literal of type %1
;followed by the definition %2
%macro MAKE_LITERAL 2
	db %1
	%2
%endmacro

%macro MAKE_LITERAL_STRING 0-*
	db T_STRING
	dq (%%end_str - %%str)
%%str:
%rep %0
	db %1
%rotate 1
%endrep
%%end_str:
%endmacro


%define MAKE_LITERAL_INT(val) MAKE_LITERAL T_INTEGER, dq val
%define MAKE_LITERAL_FLOAT(val) MAKE_LITERAL T_FLOAT, dq val
%define MAKE_LITERAL_CHAR(val) MAKE_LITERAL T_CHAR, db val
%define MAKE_LITERAL_SYMBOL(val) MAKE_LITERAL T_SYMBOL, dq val
%define MAKE_NIL db T_NIL
%define MAKE_VOID db T_VOID
%define MAKE_BOOL(val) MAKE_LITERAL T_BOOL, db val


;;; Creates a SOB with tag %2 
;;; from two pointers %3 and %4
;;; Stores result in register %1
%macro MAKE_TWO_WORDS 4 
        MALLOC %1, TYPE_SIZE+WORD_SIZE*2
        mov byte [%1], %2
        mov qword [%1+TYPE_SIZE], %3
        mov qword [%1+TYPE_SIZE+WORD_SIZE], %4
%endmacro

%macro MAKE_WORDS_LIT 3
	db %1
        dq %2
        dq %3
%endmacro

%define MAKE_PAIR(r, car, cdr) \
        MAKE_TWO_WORDS r, T_PAIR, car, cdr

%define MAKE_LITERAL_PAIR(car, cdr) \
        MAKE_WORDS_LIT T_PAIR, car, cdr

%define MAKE_CLOSURE(r, env, body) \
        MAKE_TWO_WORDS r, T_CLOSURE, env, body

	
extern printf, malloc, memmove 
global write_sob, write_sob_if_not_void

	
write_sob_undefined:
	push rbp
	mov rbp, rsp

	mov rax, 0
	mov rdi, .undefined
	call printf

	leave
	ret

section .data
.undefined:
	db "#<undefined>", 0

write_sob_integer:
	push rbp
	mov rbp, rsp

	INT_VAL rsi, rsi
	mov rdi, .int_format_string
	mov rax, 0
	call printf

	leave
	ret

section .data
.int_format_string:
	db "%ld", 0

write_sob_float:
	push rbp
	mov rbp, rsp

	FLOAT_VAL rsi, rsi
	movq xmm0, rsi
	mov rdi, .float_format_string
	mov rax, 1

	mov rsi, rsp
	and rsp, -16
	call printf
	mov rsp, rsi

	leave
	ret
	
section .data
.float_format_string:
	db "%f", 0		

write_sob_char:
	push rbp
	mov rbp, rsp

	CHAR_VAL rsi, rsi

	cmp rsi, CHAR_NUL
	je .Lnul

	cmp rsi, CHAR_TAB
	je .Ltab

	cmp rsi, CHAR_NEWLINE
	je .Lnewline

	cmp rsi, CHAR_PAGE
	je .Lpage

	cmp rsi, CHAR_RETURN
	je .Lreturn

	cmp rsi, CHAR_SPACE
	je .Lspace
	jg .Lregular

	mov rdi, .special
	jmp .done	

.Lnul:
	mov rdi, .nul
	jmp .done

.Ltab:
	mov rdi, .tab
	jmp .done

.Lnewline:
	mov rdi, .newline
	jmp .done

.Lpage:
	mov rdi, .page
	jmp .done

.Lreturn:
	mov rdi, .return
	jmp .done

.Lspace:
	mov rdi, .space
	jmp .done

.Lregular:
	mov rdi, .regular
	jmp .done

.done:
	mov rax, 0
	call printf

	leave
	ret

section .data
.space:
	db "#\space", 0
.newline:
	db "#\newline", 0
.return:
	db "#\return", 0
.tab:
	db "#\tab", 0
.page:
	db "#\page", 0
.nul:
	db "#\nul", 0
.special:
	db "#\x%02x", 0
.regular:
	db "#\%c", 0

write_sob_void:
	push rbp
	mov rbp, rsp

	mov rax, 0
	mov rdi, .void
	call printf

	leave
	ret

section .data
.void:
	db "#<void>", 0
	
write_sob_bool:
	push rbp
	mov rbp, rsp

	cmp word [rsi], SOB_FALSE
	je .sobFalse
	
	mov rdi, .true
	jmp .continue

.sobFalse:
	mov rdi, .false

.continue:
	mov rax, 0
	call printf	

	leave
	ret

section .data			
.false:
	db "#f", 0
.true:
	db "#t", 0

write_sob_nil:
	push rbp
	mov rbp, rsp

	mov rax, 0
	mov rdi, .nil
	call printf

	leave
	ret

section .data
.nil:
	db "()", 0

write_sob_string:
	push rbp
	mov rbp, rsp

	push rsi

	mov rax, 0
	mov rdi, .double_quote
	call printf
	
	pop rsi

	STRING_LENGTH rcx, rsi
	STRING_ELEMENTS rax, rsi

.loop:
	cmp rcx, 0
	je .done
	mov bl, byte [rax]
	and rbx, 0xff

	cmp rbx, CHAR_TAB
	je .ch_tab
	cmp rbx, CHAR_NEWLINE
	je .ch_newline
	cmp rbx, CHAR_PAGE
	je .ch_page
	cmp rbx, CHAR_RETURN
	je .ch_return
	cmp rbx, CHAR_DOUBLEQUOTE
	je .ch_doublequote
	cmp rbx, CHAR_BACKSLASH
	je .ch_backslash
	cmp rbx, CHAR_SPACE
	jl .ch_hex
	
	mov rdi, .fs_simple_char
	mov rsi, rbx
	jmp .printf
	
.ch_hex:
	mov rdi, .fs_hex_char
	mov rsi, rbx
	jmp .printf
	
.ch_tab:
	mov rdi, .fs_tab
	mov rsi, rbx
	jmp .printf
	
.ch_page:
	mov rdi, .fs_page
	mov rsi, rbx
	jmp .printf
	
.ch_return:
	mov rdi, .fs_return
	mov rsi, rbx
	jmp .printf

.ch_newline:
	mov rdi, .fs_newline
	mov rsi, rbx
	jmp .printf

.ch_doublequote:
	mov rdi, .fs_doublequote
	mov rsi, rbx
	jmp .printf

.ch_backslash:
	mov rdi, .fs_backslash
	mov rsi, rbx

.printf:
	push rax
	push rcx
	mov rax, 0
	call printf
	pop rcx
	pop rax

	dec rcx
	inc rax
	jmp .loop

.done:
	mov rax, 0
	mov rdi, .double_quote
	call printf

	leave
	ret
section .data
.double_quote:
	db CHAR_DOUBLEQUOTE, 0
.fs_simple_char:
	db "%c", 0
.fs_hex_char:
	db "\x%02x;", 0	
.fs_tab:
	db "\t", 0
.fs_page:
	db "\f", 0
.fs_return:
	db "\r", 0
.fs_newline:
	db "\n", 0
.fs_doublequote:
	db CHAR_BACKSLASH, CHAR_DOUBLEQUOTE, 0
.fs_backslash:
	db CHAR_BACKSLASH, CHAR_BACKSLASH, 0

write_sob_pair:
	push rbp
	mov rbp, rsp

	push rsi
	
	mov rax, 0
	mov rdi, .open_paren
	call printf

	mov rsi, [rsp]

	CAR rsi, rsi
	call write_sob

	mov rsi, [rsp]
	CDR rsi, rsi
	call write_sob_pair_on_cdr
	
	add rsp, 1*8
	
	mov rdi, .close_paren
	mov rax, 0
	call printf

	leave
	ret

section .data
.open_paren:
	db "(", 0
.close_paren:
	db ")", 0

write_sob_pair_on_cdr:
	push rbp
	mov rbp, rsp

	mov bl, byte [rsi]
	cmp bl, T_NIL
	je .done
	
	cmp bl, T_PAIR
	je .cdrIsPair
	
	push rsi
	
	mov rax, 0
	mov rdi, .dot
	call printf
	
	pop rsi

	call write_sob
	jmp .done

.cdrIsPair:
	CDR rbx, rsi
	push rbx
	CAR rsi, rsi
	push rsi
	
	mov rax, 0
	mov rdi, .space
	call printf
	
	pop rsi
	call write_sob

	pop rsi
	call write_sob_pair_on_cdr

	add rsp, 1*8

.done:
	leave
	ret

section .data
.space:
	db " ", 0
.dot:
	db " . ", 0

write_sob_symbol:
	push rbp
	mov rbp, rsp

	SYMBOL_VAL rsi, rsi
	
	STRING_LENGTH rcx, rsi
	STRING_ELEMENTS rax, rsi

	mov rdx, rcx

.loop:
	cmp rcx, 0
	je .done
	mov bl, byte [rax]
	and rbx, 0xff

	cmp rcx, rdx
	jne .ch_simple
	cmp rbx, '+'
	je .ch_hex
	cmp rbx, '-'
	je .ch_hex
	cmp rbx, 'A'
	jl .ch_hex

.ch_simple:
	mov rdi, .fs_simple_char
	mov rsi, rbx
	jmp .printf
	
.ch_hex:
	mov rdi, .fs_hex_char
	mov rsi, rbx

.printf:
	push rax
	push rcx
	mov rax, 0
	call printf
	pop rcx
	pop rax

	dec rcx
	inc rax
	jmp .loop

.done:
	leave
	ret
	
section .data
.fs_simple_char:
	db "%c", 0
.fs_hex_char:
	db "\x%02x;", 0	

write_sob_closure:
	push rbp
	mov rbp, rsp

	CLOSURE_CODE rdx, rsi
	CLOSURE_ENV rsi, rsi

	mov rdi, .closure
	mov rax, 0
	call printf

	leave
	ret
section .data
.closure:
	db "#<closure [env:%p, code:%p]>", 0

section .text
write_sob:
	mov rbx, 0
	mov bl, byte [rsi]	
	jmp qword [.jmp_table + rbx * 8]
	

section .data
.jmp_table:
	dq write_sob_undefined, write_sob_void, write_sob_nil
	dq write_sob_integer, write_sob_float, write_sob_bool
	dq write_sob_char, write_sob_string, write_sob_symbol
	dq write_sob_closure, write_sob_pair

section .text
write_sob_if_not_void:
	mov rsi, rax
	mov bl, byte [rsi]
	cmp bl, SOB_VOID
	je .continue

	call write_sob
	
	mov rax, 0
	mov rdi, .newline
	call printf
	
.continue:
	ret
section .data
.newline:
	db CHAR_NEWLINE, 0

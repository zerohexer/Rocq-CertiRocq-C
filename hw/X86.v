(* hw/X86.v -- THE x86-64 INSTRUCTIONS A KERNEL USES, WRITTEN IN ROCQ from Intel's manual (SDM vol. 2, the opcode
   tables).  Not part of the kit's core, which knows no instruction set: this file is what a user writes for the
   processor they want -- another family is another file like this one, from that family's manual.
   Each routine below is a few bytes of machine code, put by x86_setup into narrow block CODE (a slot of 32 bytes
   each) and run through hw_run as a C function of the System V convention: arguments in rdi, rsi, rdx, rcx, r8, r9,
   results in rax, rdx.  A program calls x86_setup once, first; then the operations are ordinary Rocq functions.
   hw/build.sh puts this file's text in front of every program (so the translator and the checker see inside it); it
   also compiles on its own (rocq c -R . KQ hw/X86.v), to try an encoding with Compute. *)
Require Import KQ.KQRun.
Open Scope sint63_scope.
Local Notation CODE := 7.          (* narrow block 7: the machine code; slots 0 .. 31 this file's, 32 .. a program's *)
Definition at_slot (k : int) : int := hw_addr CODE + 32 * k.
(* bytes at offset o of slot k *)
Definition i1 (k o b0 : int) (s : mem) : mem := hw_store 1 (at_slot k + o) b0 s.
Definition i2 (k o b0 b1 : int) (s : mem) : mem := hw_store 1 (at_slot k + o + 1) b1 (i1 k o b0 s).
Definition i3 (k o b0 b1 b2 : int) (s : mem) : mem := hw_store 1 (at_slot k + o + 2) b2 (i2 k o b0 b1 s).
Definition i4 (k o b0 b1 b2 b3 : int) (s : mem) : mem := hw_store 1 (at_slot k + o + 3) b3 (i3 k o b0 b1 b2 s).
Definition i5 (k o b0 b1 b2 b3 b4 : int) (s : mem) : mem := hw_store 1 (at_slot k + o + 4) b4 (i4 k o b0 b1 b2 b3 s).
(* the ModRM byte: mod (2 bits), reg (3 bits), rm (3 bits); registers by number *)
Definition modrm (md reg rm : int) : int := (md << 6) lor (reg << 3) lor rm.
Local Notation RAX := 0.
Local Notation RCX := 1.
Local Notation RDX := 2.
Local Notation RBX := 3.
Local Notation RSP := 4.
Local Notation RSI := 6.
Local Notation RDI := 7.
Local Notation RET := 0xC3.

Definition x86_setup (s : mem) : mem :=
  let s := i2 0 0 0xFA RET s in                                (* 0  cli                       FA *)
  let s := i2 1 0 0xFB RET s in                                (* 1  sti                       FB *)
  let s := i3 2 0 0xFB 0xF4 RET s in                           (* 2  sti; hlt -- sti lets one more instruction run
                                                                     first: no interrupt slips in before hlt *)
  let s := i3 3 0 0xF3 0x90 RET s in                           (* 3  pause                     F3 90 *)
  let s := i4 4 0 0x0F 0x22 (modrm 3 3 RDI) RET s in           (* 4  mov cr3, rdi              0F 22 /r *)
  let s := i4 5 0 0x0F 0x20 (modrm 3 3 RAX) RET s in           (* 5  mov rax, cr3              0F 20 /r *)
  let s := i4 6 0 0x0F 0x01 (modrm 0 7 RDI) RET s in           (* 6  invlpg [rdi]              0F 01 /7 *)
  let s := i3 7 0 0x0F 0x20 (modrm 3 3 RAX) s in               (* 7  mov rax, cr3 *)
  let s := i4 7 3 0x0F 0x22 (modrm 3 3 RAX) RET s in           (*    mov cr3, rax: every page forgotten *)
  let s := i4 8 0 0x0F 0x20 (modrm 3 2 RAX) RET s in           (* 8  mov rax, cr2: the address that faulted *)
  let s := i4 9 0 0x48 0x83 (modrm 3 5 RSP) 16 s in            (* 9  sub rsp, 16               REX.W 83 /5 ib *)
  let s := i4 9 4 0x66 0x89 (modrm 0 RSI 4) 0x24 s in          (*    mov [rsp], si: the limit  66 89 /r, SIB [rsp] *)
  let s := i5 9 8 0x48 0x89 (modrm 1 RDI 4) 0x24 2 s in        (*    mov [rsp+2], rdi: the base, disp8 *)
  let s := i4 9 13 0x0F 0x01 (modrm 0 3 4) 0x24 s in           (*    lidt [rsp]                0F 01 /3 *)
  let s := i5 9 17 0x48 0x83 (modrm 3 0 RSP) 16 RET s in       (*    add rsp, 16               REX.W 83 /0 ib *)
  let s := i2 10 0 0x89 (modrm 3 RDI RCX) s in                 (* 10 mov ecx, edi              89 /r *)
  let s := i3 10 2 0x0F 0x32 RET s in                          (*    rdmsr: edx:eax -> rdx, rax *)
  let s := i4 11 0 0x89 (modrm 3 RDI RCX) 0x89 (modrm 3 RSI RAX) s in   (* 11 mov ecx, edi; mov eax, esi *)
  let s := i3 11 4 0x0F 0x30 RET s in                          (*    wrmsr (edx: the third argument already) *)
  let s := i3 12 0 0x0F 0x31 RET s in                          (* 12 rdtsc: edx:eax -> rdx, rax *)
  let s := i4 13 0 0x31 (modrm 3 RAX RAX) 0x89 (modrm 3 RDI RDX) s in   (* 13 xor eax, eax; mov edx, edi *)
  let s := i2 13 4 0xEC RET s in                               (*    in al, dx                 EC *)
  let s := i4 14 0 0x31 (modrm 3 RAX RAX) 0x89 (modrm 3 RDI RDX) s in   (* 14 the same, *)
  let s := i3 14 4 0x66 0xED RET s in                          (*    in ax, dx                 66 ED *)
  let s := i4 15 0 0x89 (modrm 3 RDI RDX) 0xED RET s in        (* 15 mov edx, edi; in eax, dx  ED *)
  let s := i4 16 0 0x89 (modrm 3 RDI RDX) 0x89 (modrm 3 RSI RAX) s in   (* 16 mov edx, edi; mov eax, esi *)
  let s := i2 16 4 0xEE RET s in                               (*    out dx, al                EE *)
  let s := i4 17 0 0x89 (modrm 3 RDI RDX) 0x89 (modrm 3 RSI RAX) s in
  let s := i3 17 4 0x66 0xEF RET s in                          (* 17 .. out dx, ax             66 EF *)
  let s := i4 18 0 0x89 (modrm 3 RDI RDX) 0x89 (modrm 3 RSI RAX) s in
  let s := i2 18 4 0xEF RET s in                               (* 18 .. out dx, eax            EF *)
  let s := i5 19 0 (0x50 + RBX) 0x89 (modrm 3 RDI RAX) 0x89 (modrm 3 RSI RCX) s in   (* 19 push rbx; mov eax, edi;
                                                                     mov ecx, esi (rbx is the caller's: kept) *)
  let s := i4 19 5 0x0F 0xA2 0x89 (modrm 3 RBX RDX) s in       (*    cpuid; mov edx, ebx      0F A2 *)
  let s := i2 19 9 (0x58 + RBX) RET s in                       (*    pop rbx: eax, ebx -> rax, rdx *)
  let s := i5 20 0 (0x50 + RBX) 0x89 (modrm 3 RDI RAX) 0x89 (modrm 3 RSI RCX) s in   (* 20 the same, *)
  let s := i4 20 5 0x0F 0xA2 0x89 (modrm 3 RCX RAX) s in       (*    cpuid; mov eax, ecx *)
  let s := i2 20 9 (0x58 + RBX) RET s in                       (*    pop rbx: ecx, edx -> rax, rdx *)
  let s := i4 21 0 0x0F 0x20 (modrm 3 0 RAX) RET s in          (* 21 mov rax, cr0 *)
  let s := i4 22 0 0x0F 0x20 (modrm 3 2 RAX) RET s in          (* 22 mov rax, cr2 *)
  let s := i4 23 0 0x0F 0x20 (modrm 3 3 RAX) RET s in          (* 23 mov rax, cr3 *)
  let s := i4 24 0 0x0F 0x20 (modrm 3 4 RAX) RET s in          (* 24 mov rax, cr4 *)
  let s := i4 25 0 0x0F 0x22 (modrm 3 0 RDI) RET s in          (* 25 mov cr0, rdi *)
  let s := i4 26 0 0x0F 0x22 (modrm 3 3 RDI) RET s in          (* 26 mov cr3, rdi *)
  let s := i4 27 0 0x0F 0x22 (modrm 3 4 RDI) RET s in          (* 27 mov cr4, rdi *)
  hw_code_sync (at_slot 0) 1024 s.

(* ---- the operations: what the program calls.  Results go into cells of a wide block (h, i), as hw_load's do. *)
Definition run0 (k x0 x1 x2 : int) (s : mem) : mem := hw_run 0 (at_slot k) x0 x1 x2 0 0 0 0 0 s.
Definition hw_irq_off (s : mem) : mem := run0 0 0 0 0 s.
Definition hw_irq_on (s : mem) : mem := run0 1 0 0 0 s.
Definition hw_irq_wait (s : mem) : mem := run0 2 0 0 0 s.             (* interrupts on, and wait for one *)
Definition hw_pause (s : mem) : mem := run0 3 0 0 0 s.
Definition hw_pt_set (a : int) (s : mem) : mem := run0 4 a 0 0 s.       (* the page tables' root *)
Definition hw_pt_get (h i : int) (s : mem) : mem := hw_run 1 (at_slot 5) 0 0 0 0 0 0 h i s.
Definition hw_tlb_page (a : int) (s : mem) : mem := run0 6 a 0 0 s.
Definition hw_tlb_all (s : mem) : mem := run0 7 0 0 0 s.
Definition hw_fault_addr (h i : int) (s : mem) : mem := hw_run 1 (at_slot 8) 0 0 0 0 0 0 h i s.
Definition hw_vectors (a lim : int) (s : mem) : mem := run0 9 a lim 0 s. (* the interrupt table at a, lim + 1 bytes *)
Definition hw_sysreg_get (n h i : int) (s : mem) : mem := hw_run 2 (at_slot 10) n 0 0 0 0 0 h i s.  (* MSR n: low, high *)
Definition hw_sysreg_set (n lo hi : int) (s : mem) : mem := run0 11 n lo hi s.
Definition hw_cycles (h i : int) (s : mem) : mem := hw_run 2 (at_slot 12) 0 0 0 0 0 0 h i s.        (* low, high *)
Definition hw_port_in (w p h i : int) (s : mem) : mem :=
  hw_run 1 (at_slot (if w =? 1 then 13 else if w =? 2 then 14 else 15)) p 0 0 0 0 0 h i s.
Definition hw_port_out (w p v : int) (s : mem) : mem := run0 (if w =? 1 then 16 else if w =? 2 then 17 else 18) p v 0 s.
Definition hw_cpuid (leaf sub h i : int) (s : mem) : mem :=               (* eax ebx ecx edx into cells i .. i + 3 *)
  hw_run 2 (at_slot 20) leaf sub 0 0 0 0 h (i + 2) (hw_run 2 (at_slot 19) leaf sub 0 0 0 0 h i s).
Definition hw_cr_get (n h i : int) (s : mem) : mem :=                     (* control register 0, 2, 3 or 4 *)
  if n =? 0 then hw_run 1 (at_slot 21) 0 0 0 0 0 0 h i s
  else if n =? 2 then hw_run 1 (at_slot 22) 0 0 0 0 0 0 h i s
  else if n =? 3 then hw_run 1 (at_slot 23) 0 0 0 0 0 0 h i s
  else if n =? 4 then hw_run 1 (at_slot 24) 0 0 0 0 0 0 h i s else s.
Definition hw_cr_set (n v : int) (s : mem) : mem :=                       (* control register 0, 3 or 4 *)
  if n =? 0 then run0 25 v 0 0 s else if n =? 3 then run0 26 v 0 0 s else if n =? 4 then run0 27 v 0 0 s else s.

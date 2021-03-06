; NOTE: Assertions have been autogenerated by utils/update_test_checks.py
; RUN: opt < %s -instsimplify -S | FileCheck %s

define float @fadd_undef_op0(float %x) {
; CHECK-LABEL: @fadd_undef_op0(
; CHECK-NEXT:    [[R:%.*]] = fadd float undef, [[X:%.*]]
; CHECK-NEXT:    ret float [[R]]
;
  %r = fadd float undef, %x
  ret float %r
}

define float @fadd_undef_op1(float %x) {
; CHECK-LABEL: @fadd_undef_op1(
; CHECK-NEXT:    [[R:%.*]] = fadd float [[X:%.*]], undef
; CHECK-NEXT:    ret float [[R]]
;
  %r = fadd float %x, undef
  ret float %r
}

define float @fsub_undef_op0(float %x) {
; CHECK-LABEL: @fsub_undef_op0(
; CHECK-NEXT:    [[R:%.*]] = fsub float undef, [[X:%.*]]
; CHECK-NEXT:    ret float [[R]]
;
  %r = fsub float undef, %x
  ret float %r
}

define float @fsub_undef_op1(float %x) {
; CHECK-LABEL: @fsub_undef_op1(
; CHECK-NEXT:    [[R:%.*]] = fsub float [[X:%.*]], undef
; CHECK-NEXT:    ret float [[R]]
;
  %r = fsub float %x, undef
  ret float %r
}

define float @fmul_undef_op0(float %x) {
; CHECK-LABEL: @fmul_undef_op0(
; CHECK-NEXT:    [[R:%.*]] = fmul float undef, [[X:%.*]]
; CHECK-NEXT:    ret float [[R]]
;
  %r = fmul float undef, %x
  ret float %r
}

define float @fmul_undef_op1(float %x) {
; CHECK-LABEL: @fmul_undef_op1(
; CHECK-NEXT:    [[R:%.*]] = fmul float [[X:%.*]], undef
; CHECK-NEXT:    ret float [[R]]
;
  %r = fmul float %x, undef
  ret float %r
}

define float @fdiv_undef_op0(float %x) {
; CHECK-LABEL: @fdiv_undef_op0(
; CHECK-NEXT:    ret float undef
;
  %r = fdiv float undef, %x
  ret float %r
}

define float @fdiv_undef_op1(float %x) {
; CHECK-LABEL: @fdiv_undef_op1(
; CHECK-NEXT:    ret float undef
;
  %r = fdiv float %x, undef
  ret float %r
}

define float @frem_undef_op0(float %x) {
; CHECK-LABEL: @frem_undef_op0(
; CHECK-NEXT:    ret float undef
;
  %r = frem float undef, %x
  ret float %r
}

define float @frem_undef_op1(float %x) {
; CHECK-LABEL: @frem_undef_op1(
; CHECK-NEXT:    ret float undef
;
  %r = frem float %x, undef
  ret float %r
}


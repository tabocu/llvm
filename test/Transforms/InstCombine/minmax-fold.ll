; NOTE: Assertions have been autogenerated by utils/update_test_checks.py
; RUN: opt -S -instcombine < %s | FileCheck %s

; This is the canonical form for a type-changing min/max.
define i64 @t1(i32 %a) {
; CHECK-LABEL: @t1(
; CHECK-NEXT:    [[TMP1:%.*]] = icmp slt i32 [[A:%.*]], 5
; CHECK-NEXT:    [[TMP2:%.*]] = select i1 [[TMP1]], i32 [[A]], i32 5
; CHECK-NEXT:    [[TMP3:%.*]] = sext i32 [[TMP2]] to i64
; CHECK-NEXT:    ret i64 [[TMP3]]
;
  %1 = icmp slt i32 %a, 5
  %2 = select i1 %1, i32 %a, i32 5
  %3 = sext i32 %2 to i64
  ret i64 %3
}

; Check this is converted into canonical form, as above.
define i64 @t2(i32 %a) {
; CHECK-LABEL: @t2(
; CHECK-NEXT:    [[TMP1:%.*]] = icmp slt i32 [[A:%.*]], 5
; CHECK-NEXT:    [[TMP2:%.*]] = select i1 [[TMP1]], i32 [[A]], i32 5
; CHECK-NEXT:    [[TMP3:%.*]] = sext i32 [[TMP2]] to i64
; CHECK-NEXT:    ret i64 [[TMP3]]
;
  %1 = icmp slt i32 %a, 5
  %2 = sext i32 %a to i64
  %3 = select i1 %1, i64 %2, i64 5
  ret i64 %3
}

; Same as @t2, with flipped operands and zext instead of sext.
define i64 @t3(i32 %a) {
; CHECK-LABEL: @t3(
; CHECK-NEXT:    [[TMP1:%.*]] = icmp ugt i32 [[A:%.*]], 5
; CHECK-NEXT:    [[TMP2:%.*]] = select i1 [[TMP1]], i32 [[A]], i32 5
; CHECK-NEXT:    [[TMP3:%.*]] = zext i32 [[TMP2]] to i64
; CHECK-NEXT:    ret i64 [[TMP3]]
;
  %1 = icmp ult i32 %a, 5
  %2 = zext i32 %a to i64
  %3 = select i1 %1, i64 5, i64 %2
  ret i64 %3
}

; Same again, with trunc.
define i32 @t4(i64 %a) {
; CHECK-LABEL: @t4(
; CHECK-NEXT:    [[TMP1:%.*]] = icmp slt i64 [[A:%.*]], 5
; CHECK-NEXT:    [[TMP2:%.*]] = select i1 [[TMP1]], i64 [[A]], i64 5
; CHECK-NEXT:    [[TMP3:%.*]] = trunc i64 [[TMP2]] to i32
; CHECK-NEXT:    ret i32 [[TMP3]]
;
  %1 = icmp slt i64 %a, 5
  %2 = trunc i64 %a to i32
  %3 = select i1 %1, i32 %2, i32 5
  ret i32 %3
}

; Same as @t3, but with mismatched signedness between icmp and zext.
; InstCombine should leave this alone.
define i64 @t5(i32 %a) {
; CHECK-LABEL: @t5(
; CHECK-NEXT:    [[TMP1:%.*]] = icmp slt i32 [[A:%.*]], 5
; CHECK-NEXT:    [[TMP2:%.*]] = zext i32 [[A]] to i64
; CHECK-NEXT:    [[TMP3:%.*]] = select i1 [[TMP1]], i64 5, i64 [[TMP2]]
; CHECK-NEXT:    ret i64 [[TMP3]]
;
  %1 = icmp slt i32 %a, 5
  %2 = zext i32 %a to i64
  %3 = select i1 %1, i64 5, i64 %2
  ret i64 %3
}

define float @t6(i32 %a) {
; CHECK-LABEL: @t6(
; CHECK-NEXT:    [[TMP1:%.*]] = icmp slt i32 [[A:%.*]], 0
; CHECK-NEXT:    [[TMP2:%.*]] = select i1 [[TMP1]], i32 [[A]], i32 0
; CHECK-NEXT:    [[TMP3:%.*]] = sitofp i32 [[TMP2]] to float
; CHECK-NEXT:    ret float [[TMP3]]
;
  %1 = icmp slt i32 %a, 0
  %2 = select i1 %1, i32 %a, i32 0
  %3 = sitofp i32 %2 to float
  ret float %3
}

define i16 @t7(i32 %a) {
; CHECK-LABEL: @t7(
; CHECK-NEXT:    [[TMP1:%.*]] = icmp slt i32 [[A:%.*]], -32768
; CHECK-NEXT:    [[TMP2:%.*]] = select i1 [[TMP1]], i32 [[A]], i32 -32768
; CHECK-NEXT:    [[TMP3:%.*]] = trunc i32 [[TMP2]] to i16
; CHECK-NEXT:    ret i16 [[TMP3]]
;
  %1 = icmp slt i32 %a, -32768
  %2 = trunc i32 %a to i16
  %3 = select i1 %1, i16 %2, i16 -32768
  ret i16 %3
}

; Just check for no infinite loop. InstSimplify liked to
; "simplify" -32767 by removing all the sign bits,
; which led to a canonicalization fight between different
; parts of instcombine.
define i32 @t8(i64 %a, i32 %b) {
; CHECK-LABEL: @t8(
; CHECK-NEXT:    [[TMP1:%.*]] = icmp slt i64 [[A:%.*]], -32767
; CHECK-NEXT:    [[TMP2:%.*]] = select i1 [[TMP1]], i64 [[A]], i64 -32767
; CHECK-NEXT:    [[TMP3:%.*]] = trunc i64 [[TMP2]] to i32
; CHECK-NEXT:    [[TMP4:%.*]] = icmp slt i32 [[B:%.*]], 42
; CHECK-NEXT:    [[TMP5:%.*]] = select i1 [[TMP4]], i32 42, i32 [[TMP3]]
; CHECK-NEXT:    [[TMP6:%.*]] = icmp ne i32 [[TMP5]], [[B]]
; CHECK-NEXT:    [[TMP7:%.*]] = zext i1 [[TMP6]] to i32
; CHECK-NEXT:    ret i32 [[TMP7]]
;
  %1 = icmp slt i64 %a, -32767
  %2 = select i1 %1, i64 %a, i64 -32767
  %3 = trunc i64 %2 to i32
  %4 = icmp slt i32 %b, 42
  %5 = select i1 %4, i32 42, i32 %3
  %6 = icmp ne i32 %5, %b
  %7 = zext i1 %6 to i32
  ret i32 %7
}

; Ensure this doesn't get converted to a min/max.
define i64 @t9(i32 %a) {
; CHECK-LABEL: @t9(
; CHECK-NEXT:    [[TMP1:%.*]] = icmp sgt i32 [[A:%.*]], -1
; CHECK-NEXT:    [[TMP2:%.*]] = sext i32 [[A]] to i64
; CHECK-NEXT:    [[TMP3:%.*]] = select i1 [[TMP1]], i64 [[TMP2]], i64 4294967295
; CHECK-NEXT:    ret i64 [[TMP3]]
;
  %1 = icmp sgt i32 %a, -1
  %2 = sext i32 %a to i64
  %3 = select i1 %1, i64 %2, i64 4294967295
  ret i64 %3
}

define float @t10(i32 %x) {
; CHECK-LABEL: @t10(
; CHECK-NEXT:    [[TMP1:%.*]] = icmp sgt i32 [[X:%.*]], 255
; CHECK-NEXT:    [[R1:%.*]] = select i1 [[TMP1]], i32 [[X]], i32 255
; CHECK-NEXT:    [[TMP2:%.*]] = sitofp i32 [[R1]] to float
; CHECK-NEXT:    ret float [[TMP2]]
;
  %f_x = sitofp i32 %x to float
  %cmp = icmp sgt i32 %x, 255
  %r = select i1 %cmp, float %f_x, float 255.0
  ret float %r
}

define float @t11(i64 %x) {
; CHECK-LABEL: @t11(
; CHECK-NEXT:    [[TMP1:%.*]] = icmp sgt i64 [[X:%.*]], 255
; CHECK-NEXT:    [[R1:%.*]] = select i1 [[TMP1]], i64 [[X]], i64 255
; CHECK-NEXT:    [[TMP2:%.*]] = sitofp i64 [[R1]] to float
; CHECK-NEXT:    ret float [[TMP2]]
;
  %f_x = sitofp i64 %x to float
  %cmp = icmp sgt i64 %x, 255
  %r = select i1 %cmp, float %f_x, float 255.0
  ret float %r
}

; Reuse the first 2 bitcasts as the select operands.

define <4 x i32> @bitcasts_fcmp_1(<2 x i64> %a, <2 x i64> %b) {
; CHECK-LABEL: @bitcasts_fcmp_1(
; CHECK-NEXT:    [[T0:%.*]] = bitcast <2 x i64> [[A:%.*]] to <4 x float>
; CHECK-NEXT:    [[T1:%.*]] = bitcast <2 x i64> [[B:%.*]] to <4 x float>
; CHECK-NEXT:    [[T2:%.*]] = fcmp olt <4 x float> [[T1]], [[T0]]
; CHECK-NEXT:    [[TMP1:%.*]] = select <4 x i1> [[T2]], <4 x float> [[T0]], <4 x float> [[T1]]
; CHECK-NEXT:    [[T5:%.*]] = bitcast <4 x float> [[TMP1]] to <4 x i32>
; CHECK-NEXT:    ret <4 x i32> [[T5]]
;
  %t0 = bitcast <2 x i64> %a to <4 x float>
  %t1 = bitcast <2 x i64> %b to <4 x float>
  %t2 = fcmp olt <4 x float> %t1, %t0
  %t3 = bitcast <2 x i64> %a to <4 x i32>
  %t4 = bitcast <2 x i64> %b to <4 x i32>
  %t5 = select <4 x i1> %t2, <4 x i32> %t3, <4 x i32> %t4
  ret <4 x i32> %t5
}

; Switch cmp operand order.

define <4 x i32> @bitcasts_fcmp_2(<2 x i64> %a, <2 x i64> %b) {
; CHECK-LABEL: @bitcasts_fcmp_2(
; CHECK-NEXT:    [[T0:%.*]] = bitcast <2 x i64> [[A:%.*]] to <4 x float>
; CHECK-NEXT:    [[T1:%.*]] = bitcast <2 x i64> [[B:%.*]] to <4 x float>
; CHECK-NEXT:    [[T2:%.*]] = fcmp olt <4 x float> [[T0]], [[T1]]
; CHECK-NEXT:    [[TMP1:%.*]] = select <4 x i1> [[T2]], <4 x float> [[T0]], <4 x float> [[T1]]
; CHECK-NEXT:    [[T5:%.*]] = bitcast <4 x float> [[TMP1]] to <4 x i32>
; CHECK-NEXT:    ret <4 x i32> [[T5]]
;
  %t0 = bitcast <2 x i64> %a to <4 x float>
  %t1 = bitcast <2 x i64> %b to <4 x float>
  %t2 = fcmp olt <4 x float> %t0, %t1
  %t3 = bitcast <2 x i64> %a to <4 x i32>
  %t4 = bitcast <2 x i64> %b to <4 x i32>
  %t5 = select <4 x i1> %t2, <4 x i32> %t3, <4 x i32> %t4
  ret <4 x i32> %t5
}

; Integer cmp should have the same transforms.

define <4 x float> @bitcasts_icmp(<2 x i64> %a, <2 x i64> %b) {
; CHECK-LABEL: @bitcasts_icmp(
; CHECK-NEXT:    [[T0:%.*]] = bitcast <2 x i64> [[A:%.*]] to <4 x i32>
; CHECK-NEXT:    [[T1:%.*]] = bitcast <2 x i64> [[B:%.*]] to <4 x i32>
; CHECK-NEXT:    [[T2:%.*]] = icmp slt <4 x i32> [[T1]], [[T0]]
; CHECK-NEXT:    [[TMP1:%.*]] = select <4 x i1> [[T2]], <4 x i32> [[T0]], <4 x i32> [[T1]]
; CHECK-NEXT:    [[T5:%.*]] = bitcast <4 x i32> [[TMP1]] to <4 x float>
; CHECK-NEXT:    ret <4 x float> [[T5]]
;
  %t0 = bitcast <2 x i64> %a to <4 x i32>
  %t1 = bitcast <2 x i64> %b to <4 x i32>
  %t2 = icmp slt <4 x i32> %t1, %t0
  %t3 = bitcast <2 x i64> %a to <4 x float>
  %t4 = bitcast <2 x i64> %b to <4 x float>
  %t5 = select <4 x i1> %t2, <4 x float> %t3, <4 x float> %t4
  ret <4 x float> %t5
}

; SMIN(SMIN(X, 11), 92) -> SMIN(X, 11)
define i32 @test68(i32 %x) {
; CHECK-LABEL: @test68(
; CHECK-NEXT:    [[TMP1:%.*]] = icmp slt i32 [[X:%.*]], 11
; CHECK-NEXT:    [[COND:%.*]] = select i1 [[TMP1]], i32 [[X]], i32 11
; CHECK-NEXT:    ret i32 [[COND]]
;
  %cmp = icmp slt i32 11, %x
  %cond = select i1 %cmp, i32 11, i32 %x
  %cmp3 = icmp slt i32 92, %cond
  %retval = select i1 %cmp3, i32 92, i32 %cond
  ret i32 %retval
}

define <2 x i32> @test68vec(<2 x i32> %x) {
; CHECK-LABEL: @test68vec(
; CHECK-NEXT:    [[TMP1:%.*]] = icmp slt <2 x i32> [[X:%.*]], <i32 11, i32 11>
; CHECK-NEXT:    [[COND:%.*]] = select <2 x i1> [[TMP1]], <2 x i32> [[X]], <2 x i32> <i32 11, i32 11>
; CHECK-NEXT:    ret <2 x i32> [[COND]]
;
  %cmp = icmp slt <2 x i32> <i32 11, i32 11>, %x
  %cond = select <2 x i1> %cmp, <2 x i32> <i32 11, i32 11>, <2 x i32> %x
  %cmp3 = icmp slt <2 x i32> <i32 92, i32 92>, %cond
  %retval = select <2 x i1> %cmp3, <2 x i32> <i32 92, i32 92>, <2 x i32> %cond
  ret <2 x i32> %retval
}

; MIN(MIN(X, 24), 83) -> MIN(X, 24)
define i32 @test69(i32 %x) {
; CHECK-LABEL: @test69(
; CHECK-NEXT:    [[TMP1:%.*]] = icmp ult i32 [[X:%.*]], 24
; CHECK-NEXT:    [[COND:%.*]] = select i1 [[TMP1]], i32 [[X]], i32 24
; CHECK-NEXT:    ret i32 [[COND]]
;
  %cmp = icmp ult i32 24, %x
  %cond = select i1 %cmp, i32 24, i32 %x
  %cmp3 = icmp ult i32 83, %cond
  %retval = select i1 %cmp3, i32 83, i32 %cond
  ret i32 %retval
}

; SMAX(SMAX(X, 75), 36) -> SMAX(X, 75)
define i32 @test70(i32 %x) {
; CHECK-LABEL: @test70(
; CHECK-NEXT:    [[TMP1:%.*]] = icmp sgt i32 [[X:%.*]], 75
; CHECK-NEXT:    [[COND:%.*]] = select i1 [[TMP1]], i32 [[X]], i32 75
; CHECK-NEXT:    ret i32 [[COND]]
;
  %cmp = icmp slt i32 %x, 75
  %cond = select i1 %cmp, i32 75, i32 %x
  %cmp3 = icmp slt i32 %cond, 36
  %retval = select i1 %cmp3, i32 36, i32 %cond
  ret i32 %retval
}

; MAX(MAX(X, 68), 47) -> MAX(X, 68)
define i32 @test71(i32 %x) {
; CHECK-LABEL: @test71(
; CHECK-NEXT:    [[TMP1:%.*]] = icmp ugt i32 [[X:%.*]], 68
; CHECK-NEXT:    [[COND:%.*]] = select i1 [[TMP1]], i32 [[X]], i32 68
; CHECK-NEXT:    ret i32 [[COND]]
;
  %cmp = icmp ult i32 %x, 68
  %cond = select i1 %cmp, i32 68, i32 %x
  %cmp3 = icmp ult i32 %cond, 47
  %retval = select i1 %cmp3, i32 47, i32 %cond
  ret i32 %retval
}

; SMIN(SMIN(X, 92), 11) -> SMIN(X, 11)
define i32 @test72(i32 %x) {
; CHECK-LABEL: @test72(
; CHECK-NEXT:    [[TMP1:%.*]] = icmp slt i32 [[X:%.*]], 11
; CHECK-NEXT:    [[RETVAL:%.*]] = select i1 [[TMP1]], i32 [[X]], i32 11
; CHECK-NEXT:    ret i32 [[RETVAL]]
;
  %cmp = icmp sgt i32 %x, 92
  %cond = select i1 %cmp, i32 92, i32 %x
  %cmp3 = icmp sgt i32 %cond, 11
  %retval = select i1 %cmp3, i32 11, i32 %cond
  ret i32 %retval
}

define <2 x i32> @test72vec(<2 x i32> %x) {
; CHECK-LABEL: @test72vec(
; CHECK-NEXT:    [[TMP1:%.*]] = icmp slt <2 x i32> [[X:%.*]], <i32 11, i32 11>
; CHECK-NEXT:    [[RETVAL:%.*]] = select <2 x i1> [[TMP1]], <2 x i32> [[X]], <2 x i32> <i32 11, i32 11>
; CHECK-NEXT:    ret <2 x i32> [[RETVAL]]
;
  %cmp = icmp sgt <2 x i32> %x, <i32 92, i32 92>
  %cond = select <2 x i1> %cmp, <2 x i32> <i32 92, i32 92>, <2 x i32> %x
  %cmp3 = icmp sgt <2 x i32> %cond, <i32 11, i32 11>
  %retval = select <2 x i1> %cmp3, <2 x i32> <i32 11, i32 11>, <2 x i32> %cond
  ret <2 x i32> %retval
}

; MIN(MIN(X, 83), 24) -> MIN(X, 24)
define i32 @test73(i32 %x) {
; CHECK-LABEL: @test73(
; CHECK-NEXT:    [[TMP1:%.*]] = icmp ult i32 [[X:%.*]], 24
; CHECK-NEXT:    [[RETVAL:%.*]] = select i1 [[TMP1]], i32 [[X]], i32 24
; CHECK-NEXT:    ret i32 [[RETVAL]]
;
  %cmp = icmp ugt i32 %x, 83
  %cond = select i1 %cmp, i32 83, i32 %x
  %cmp3 = icmp ugt i32 %cond, 24
  %retval = select i1 %cmp3, i32 24, i32 %cond
  ret i32 %retval
}

; SMAX(SMAX(X, 36), 75) -> SMAX(X, 75)
define i32 @test74(i32 %x) {
; CHECK-LABEL: @test74(
; CHECK-NEXT:    [[TMP1:%.*]] = icmp sgt i32 [[X:%.*]], 75
; CHECK-NEXT:    [[RETVAL:%.*]] = select i1 [[TMP1]], i32 [[X]], i32 75
; CHECK-NEXT:    ret i32 [[RETVAL]]
;
  %cmp = icmp slt i32 %x, 36
  %cond = select i1 %cmp, i32 36, i32 %x
  %cmp3 = icmp slt i32 %cond, 75
  %retval = select i1 %cmp3, i32 75, i32 %cond
  ret i32 %retval
}

; MAX(MAX(X, 47), 68) -> MAX(X, 68)
define i32 @test75(i32 %x) {
; CHECK-LABEL: @test75(
; CHECK-NEXT:    [[TMP1:%.*]] = icmp ugt i32 [[X:%.*]], 68
; CHECK-NEXT:    [[RETVAL:%.*]] = select i1 [[TMP1]], i32 [[X]], i32 68
; CHECK-NEXT:    ret i32 [[RETVAL]]
;
  %cmp = icmp ult i32 %x, 47
  %cond = select i1 %cmp, i32 47, i32 %x
  %cmp3 = icmp ult i32 %cond, 68
  %retval = select i1 %cmp3, i32 68, i32 %cond
  ret i32 %retval
}

; The next 10 tests are value clamping with constants:
; https://llvm.org/bugs/show_bug.cgi?id=31693

; (X <s C1) ? C1 : SMIN(X, C2) ==> SMAX(SMIN(X, C2), C1)

define i32 @clamp_signed1(i32 %x) {
; CHECK-LABEL: @clamp_signed1(
; CHECK-NEXT:    [[CMP2:%.*]] = icmp slt i32 [[X:%.*]], 255
; CHECK-NEXT:    [[MIN:%.*]] = select i1 [[CMP2]], i32 [[X]], i32 255
; CHECK-NEXT:    [[TMP1:%.*]] = icmp sgt i32 [[MIN]], 15
; CHECK-NEXT:    [[R:%.*]] = select i1 [[TMP1]], i32 [[MIN]], i32 15
; CHECK-NEXT:    ret i32 [[R]]
;
  %cmp2 = icmp slt i32 %x, 255
  %min = select i1 %cmp2, i32 %x, i32 255
  %cmp1 = icmp slt i32 %x, 15
  %r = select i1 %cmp1, i32 15, i32 %min
  ret i32 %r
}

; (X >s C1) ? C1 : SMAX(X, C2) ==> SMIN(SMAX(X, C2), C1)

define i32 @clamp_signed2(i32 %x) {
; CHECK-LABEL: @clamp_signed2(
; CHECK-NEXT:    [[CMP2:%.*]] = icmp sgt i32 [[X:%.*]], 15
; CHECK-NEXT:    [[MAX:%.*]] = select i1 [[CMP2]], i32 [[X]], i32 15
; CHECK-NEXT:    [[TMP1:%.*]] = icmp slt i32 [[MAX]], 255
; CHECK-NEXT:    [[R:%.*]] = select i1 [[TMP1]], i32 [[MAX]], i32 255
; CHECK-NEXT:    ret i32 [[R]]
;
  %cmp2 = icmp sgt i32 %x, 15
  %max = select i1 %cmp2, i32 %x, i32 15
  %cmp1 = icmp sgt i32 %x, 255
  %r = select i1 %cmp1, i32 255, i32 %max
  ret i32 %r
}

; (X >s C1) ? SMIN(X, C2) : C1 ==> SMAX(SMIN(X, C2), C1)

define i32 @clamp_signed3(i32 %x) {
; CHECK-LABEL: @clamp_signed3(
; CHECK-NEXT:    [[CMP2:%.*]] = icmp slt i32 [[X:%.*]], 255
; CHECK-NEXT:    [[MIN:%.*]] = select i1 [[CMP2]], i32 [[X]], i32 255
; CHECK-NEXT:    [[TMP1:%.*]] = icmp sgt i32 [[MIN]], 15
; CHECK-NEXT:    [[R:%.*]] = select i1 [[TMP1]], i32 [[MIN]], i32 15
; CHECK-NEXT:    ret i32 [[R]]
;
  %cmp2 = icmp slt i32 %x, 255
  %min = select i1 %cmp2, i32 %x, i32 255
  %cmp1 = icmp sgt i32 %x, 15
  %r = select i1 %cmp1, i32 %min, i32 15
  ret i32 %r
}

; (X <s C1) ? SMAX(X, C2) : C1 ==> SMIN(SMAX(X, C1), C2)

define i32 @clamp_signed4(i32 %x) {
; CHECK-LABEL: @clamp_signed4(
; CHECK-NEXT:    [[CMP2:%.*]] = icmp sgt i32 [[X:%.*]], 15
; CHECK-NEXT:    [[MAX:%.*]] = select i1 [[CMP2]], i32 [[X]], i32 15
; CHECK-NEXT:    [[TMP1:%.*]] = icmp slt i32 [[MAX]], 255
; CHECK-NEXT:    [[R:%.*]] = select i1 [[TMP1]], i32 [[MAX]], i32 255
; CHECK-NEXT:    ret i32 [[R]]
;
  %cmp2 = icmp sgt i32 %x, 15
  %max = select i1 %cmp2, i32 %x, i32 15
  %cmp1 = icmp slt i32 %x, 255
  %r = select i1 %cmp1, i32 %max, i32 255
  ret i32 %r
}

; (X <u C1) ? C1 : UMIN(X, C2) ==> UMAX(UMIN(X, C2), C1)

define i32 @clamp_unsigned1(i32 %x) {
; CHECK-LABEL: @clamp_unsigned1(
; CHECK-NEXT:    [[CMP2:%.*]] = icmp ult i32 [[X:%.*]], 255
; CHECK-NEXT:    [[MIN:%.*]] = select i1 [[CMP2]], i32 [[X]], i32 255
; CHECK-NEXT:    [[TMP1:%.*]] = icmp ugt i32 [[MIN]], 15
; CHECK-NEXT:    [[R:%.*]] = select i1 [[TMP1]], i32 [[MIN]], i32 15
; CHECK-NEXT:    ret i32 [[R]]
;
  %cmp2 = icmp ult i32 %x, 255
  %min = select i1 %cmp2, i32 %x, i32 255
  %cmp1 = icmp ult i32 %x, 15
  %r = select i1 %cmp1, i32 15, i32 %min
  ret i32 %r
}

; (X >u C1) ? C1 : UMAX(X, C2) ==> UMIN(UMAX(X, C2), C1)

define i32 @clamp_unsigned2(i32 %x) {
; CHECK-LABEL: @clamp_unsigned2(
; CHECK-NEXT:    [[CMP2:%.*]] = icmp ugt i32 [[X:%.*]], 15
; CHECK-NEXT:    [[MAX:%.*]] = select i1 [[CMP2]], i32 [[X]], i32 15
; CHECK-NEXT:    [[TMP1:%.*]] = icmp ult i32 [[MAX]], 255
; CHECK-NEXT:    [[R:%.*]] = select i1 [[TMP1]], i32 [[MAX]], i32 255
; CHECK-NEXT:    ret i32 [[R]]
;
  %cmp2 = icmp ugt i32 %x, 15
  %max = select i1 %cmp2, i32 %x, i32 15
  %cmp1 = icmp ugt i32 %x, 255
  %r = select i1 %cmp1, i32 255, i32 %max
  ret i32 %r
}

; (X >u C1) ? UMIN(X, C2) : C1 ==> UMAX(UMIN(X, C2), C1)

define i32 @clamp_unsigned3(i32 %x) {
; CHECK-LABEL: @clamp_unsigned3(
; CHECK-NEXT:    [[CMP2:%.*]] = icmp ult i32 [[X:%.*]], 255
; CHECK-NEXT:    [[MIN:%.*]] = select i1 [[CMP2]], i32 [[X]], i32 255
; CHECK-NEXT:    [[TMP1:%.*]] = icmp ugt i32 [[MIN]], 15
; CHECK-NEXT:    [[R:%.*]] = select i1 [[TMP1]], i32 [[MIN]], i32 15
; CHECK-NEXT:    ret i32 [[R]]
;
  %cmp2 = icmp ult i32 %x, 255
  %min = select i1 %cmp2, i32 %x, i32 255
  %cmp1 = icmp ugt i32 %x, 15
  %r = select i1 %cmp1, i32 %min, i32 15
  ret i32 %r
}

; (X <u C1) ? UMAX(X, C2) : C1 ==> UMIN(UMAX(X, C2), C1)

define i32 @clamp_unsigned4(i32 %x) {
; CHECK-LABEL: @clamp_unsigned4(
; CHECK-NEXT:    [[CMP2:%.*]] = icmp ugt i32 [[X:%.*]], 15
; CHECK-NEXT:    [[MAX:%.*]] = select i1 [[CMP2]], i32 [[X]], i32 15
; CHECK-NEXT:    [[TMP1:%.*]] = icmp ult i32 [[MAX]], 255
; CHECK-NEXT:    [[R:%.*]] = select i1 [[TMP1]], i32 [[MAX]], i32 255
; CHECK-NEXT:    ret i32 [[R]]
;
  %cmp2 = icmp ugt i32 %x, 15
  %max = select i1 %cmp2, i32 %x, i32 15
  %cmp1 = icmp ult i32 %x, 255
  %r = select i1 %cmp1, i32 %max, i32 255
  ret i32 %r
}

; Check that clamp is recognized and there is no infinite
; loop because of reverse cmp transformation:
; (icmp sgt smin(PositiveA, B) 0) -> (icmp sgt B 0)
define i32 @clamp_check_for_no_infinite_loop1(i32 %i) {
; CHECK-LABEL: @clamp_check_for_no_infinite_loop1(
; CHECK-NEXT:    [[CMP1:%.*]] = icmp slt i32 [[I:%.*]], 255
; CHECK-NEXT:    [[SEL1:%.*]] = select i1 [[CMP1]], i32 [[I]], i32 255
; CHECK-NEXT:    [[TMP1:%.*]] = icmp sgt i32 [[SEL1]], 0
; CHECK-NEXT:    [[RES:%.*]] = select i1 [[TMP1]], i32 [[SEL1]], i32 0
; CHECK-NEXT:    ret i32 [[RES]]
;
  %cmp1 = icmp slt i32 %i, 255
  %sel1 = select i1 %cmp1, i32 %i, i32 255
  %cmp2 = icmp slt i32 %i, 0
  %res = select i1 %cmp2, i32 0, i32 %sel1
  ret i32 %res
}
; Check that there is no infinite loop in case of:
; (icmp slt smax(NegativeA, B) 0) -> (icmp slt B 0)
define i32 @clamp_check_for_no_infinite_loop2(i32 %i) {
; CHECK-LABEL: @clamp_check_for_no_infinite_loop2(
; CHECK-NEXT:    [[CMP1:%.*]] = icmp sgt i32 [[I:%.*]], -255
; CHECK-NEXT:    [[SEL1:%.*]] = select i1 [[CMP1]], i32 [[I]], i32 -255
; CHECK-NEXT:    [[TMP1:%.*]] = icmp slt i32 [[SEL1]], 0
; CHECK-NEXT:    [[RES:%.*]] = select i1 [[TMP1]], i32 [[SEL1]], i32 0
; CHECK-NEXT:    ret i32 [[RES]]
;
  %cmp1 = icmp sgt i32 %i, -255
  %sel1 = select i1 %cmp1, i32 %i, i32 -255
  %cmp2 = icmp slt i32 %i, 0
  %res = select i1 %cmp2, i32 %sel1, i32 0
  ret i32 %res
}

; The next 3 min tests should canonicalize to the same form...and not infinite loop.

define double @PR31751_umin1(i32 %x) {
; CHECK-LABEL: @PR31751_umin1(
; CHECK-NEXT:    [[TMP1:%.*]] = icmp ult i32 [[X:%.*]], 2147483647
; CHECK-NEXT:    [[SEL:%.*]] = select i1 [[TMP1]], i32 [[X]], i32 2147483647
; CHECK-NEXT:    [[CONV:%.*]] = sitofp i32 [[SEL]] to double
; CHECK-NEXT:    ret double [[CONV]]
;
  %cmp = icmp slt i32 %x, 0
  %sel = select i1 %cmp, i32 2147483647, i32 %x
  %conv = sitofp i32 %sel to double
  ret double %conv
}

define double @PR31751_umin2(i32 %x) {
; CHECK-LABEL: @PR31751_umin2(
; CHECK-NEXT:    [[CMP:%.*]] = icmp ult i32 [[X:%.*]], 2147483647
; CHECK-NEXT:    [[SEL:%.*]] = select i1 [[CMP]], i32 [[X]], i32 2147483647
; CHECK-NEXT:    [[CONV:%.*]] = sitofp i32 [[SEL]] to double
; CHECK-NEXT:    ret double [[CONV]]
;
  %cmp = icmp ult i32 %x, 2147483647
  %sel = select i1 %cmp, i32 %x, i32 2147483647
  %conv = sitofp i32 %sel to double
  ret double %conv
}

define double @PR31751_umin3(i32 %x) {
; CHECK-LABEL: @PR31751_umin3(
; CHECK-NEXT:    [[TMP1:%.*]] = icmp ult i32 [[X:%.*]], 2147483647
; CHECK-NEXT:    [[SEL:%.*]] = select i1 [[TMP1]], i32 [[X]], i32 2147483647
; CHECK-NEXT:    [[CONV:%.*]] = sitofp i32 [[SEL]] to double
; CHECK-NEXT:    ret double [[CONV]]
;
  %cmp = icmp ugt i32 %x, 2147483647
  %sel = select i1 %cmp, i32 2147483647, i32 %x
  %conv = sitofp i32 %sel to double
  ret double %conv
}

; The next 3 max tests should canonicalize to the same form...and not infinite loop.

define double @PR31751_umax1(i32 %x) {
; CHECK-LABEL: @PR31751_umax1(
; CHECK-NEXT:    [[TMP1:%.*]] = icmp ugt i32 [[X:%.*]], -2147483648
; CHECK-NEXT:    [[SEL:%.*]] = select i1 [[TMP1]], i32 [[X]], i32 -2147483648
; CHECK-NEXT:    [[CONV:%.*]] = sitofp i32 [[SEL]] to double
; CHECK-NEXT:    ret double [[CONV]]
;
  %cmp = icmp sgt i32 %x, -1
  %sel = select i1 %cmp, i32 2147483648, i32 %x
  %conv = sitofp i32 %sel to double
  ret double %conv
}

define double @PR31751_umax2(i32 %x) {
; CHECK-LABEL: @PR31751_umax2(
; CHECK-NEXT:    [[CMP:%.*]] = icmp ugt i32 [[X:%.*]], -2147483648
; CHECK-NEXT:    [[SEL:%.*]] = select i1 [[CMP]], i32 [[X]], i32 -2147483648
; CHECK-NEXT:    [[CONV:%.*]] = sitofp i32 [[SEL]] to double
; CHECK-NEXT:    ret double [[CONV]]
;
  %cmp = icmp ugt i32 %x, 2147483648
  %sel = select i1 %cmp, i32 %x, i32 2147483648
  %conv = sitofp i32 %sel to double
  ret double %conv
}

define double @PR31751_umax3(i32 %x) {
; CHECK-LABEL: @PR31751_umax3(
; CHECK-NEXT:    [[TMP1:%.*]] = icmp ugt i32 [[X:%.*]], -2147483648
; CHECK-NEXT:    [[SEL:%.*]] = select i1 [[TMP1]], i32 [[X]], i32 -2147483648
; CHECK-NEXT:    [[CONV:%.*]] = sitofp i32 [[SEL]] to double
; CHECK-NEXT:    ret double [[CONV]]
;
  %cmp = icmp ult i32 %x, 2147483648
  %sel = select i1 %cmp, i32 2147483648, i32 %x
  %conv = sitofp i32 %sel to double
  ret double %conv
}

; The icmp/select form a canonical smax, so don't hide that by folding the final bitcast into the select.

define float @bitcast_scalar_smax(float %x, float %y) {
; CHECK-LABEL: @bitcast_scalar_smax(
; CHECK-NEXT:    [[BCX:%.*]] = bitcast float [[X:%.*]] to i32
; CHECK-NEXT:    [[BCY:%.*]] = bitcast float [[Y:%.*]] to i32
; CHECK-NEXT:    [[CMP:%.*]] = icmp sgt i32 [[BCX]], [[BCY]]
; CHECK-NEXT:    [[SEL:%.*]] = select i1 [[CMP]], i32 [[BCX]], i32 [[BCY]]
; CHECK-NEXT:    [[BCS:%.*]] = bitcast i32 [[SEL]] to float
; CHECK-NEXT:    ret float [[BCS]]
;
  %bcx = bitcast float %x to i32
  %bcy = bitcast float %y to i32
  %cmp = icmp sgt i32 %bcx, %bcy
  %sel = select i1 %cmp, i32 %bcx, i32 %bcy
  %bcs = bitcast i32 %sel to float
  ret float %bcs
}

; FIXME: Create a canonical umax by bitcasting the select.

define float @bitcast_scalar_umax(float %x, float %y) {
; CHECK-LABEL: @bitcast_scalar_umax(
; CHECK-NEXT:    [[BCX:%.*]] = bitcast float [[X:%.*]] to i32
; CHECK-NEXT:    [[BCY:%.*]] = bitcast float [[Y:%.*]] to i32
; CHECK-NEXT:    [[CMP:%.*]] = icmp ugt i32 [[BCX]], [[BCY]]
; CHECK-NEXT:    [[SEL:%.*]] = select i1 [[CMP]], float [[X]], float [[Y]]
; CHECK-NEXT:    ret float [[SEL]]
;
  %bcx = bitcast float %x to i32
  %bcy = bitcast float %y to i32
  %cmp = icmp ugt i32 %bcx, %bcy
  %sel = select i1 %cmp, float %x, float %y
  ret float %sel
}

; PR32306 - https://bugs.llvm.org/show_bug.cgi?id=32306
; The icmp/select form a canonical smin, so don't hide that by folding the final bitcast into the select.

define <8 x float> @bitcast_vector_smin(<8 x float> %x, <8 x float> %y) {
; CHECK-LABEL: @bitcast_vector_smin(
; CHECK-NEXT:    [[BCX:%.*]] = bitcast <8 x float> [[X:%.*]] to <8 x i32>
; CHECK-NEXT:    [[BCY:%.*]] = bitcast <8 x float> [[Y:%.*]] to <8 x i32>
; CHECK-NEXT:    [[CMP:%.*]] = icmp slt <8 x i32> [[BCX]], [[BCY]]
; CHECK-NEXT:    [[SEL:%.*]] = select <8 x i1> [[CMP]], <8 x i32> [[BCX]], <8 x i32> [[BCY]]
; CHECK-NEXT:    [[BCS:%.*]] = bitcast <8 x i32> [[SEL]] to <8 x float>
; CHECK-NEXT:    ret <8 x float> [[BCS]]
;
  %bcx = bitcast <8 x float> %x to <8 x i32>
  %bcy = bitcast <8 x float> %y to <8 x i32>
  %cmp = icmp slt <8 x i32> %bcx, %bcy
  %sel = select <8 x i1> %cmp, <8 x i32> %bcx, <8 x i32> %bcy
  %bcs = bitcast <8 x i32> %sel to <8 x float>
  ret <8 x float> %bcs
}

; FIXME: Create a canonical umin by bitcasting the select.

define <8 x float> @bitcast_vector_umin(<8 x float> %x, <8 x float> %y) {
; CHECK-LABEL: @bitcast_vector_umin(
; CHECK-NEXT:    [[BCX:%.*]] = bitcast <8 x float> [[X:%.*]] to <8 x i32>
; CHECK-NEXT:    [[BCY:%.*]] = bitcast <8 x float> [[Y:%.*]] to <8 x i32>
; CHECK-NEXT:    [[CMP:%.*]] = icmp slt <8 x i32> [[BCX]], [[BCY]]
; CHECK-NEXT:    [[SEL:%.*]] = select <8 x i1> [[CMP]], <8 x float> [[X]], <8 x float> [[Y]]
; CHECK-NEXT:    ret <8 x float> [[SEL]]
;
  %bcx = bitcast <8 x float> %x to <8 x i32>
  %bcy = bitcast <8 x float> %y to <8 x i32>
  %cmp = icmp slt <8 x i32> %bcx, %bcy
  %sel = select <8 x i1> %cmp, <8 x float> %x, <8 x float> %y
  ret <8 x float> %sel
}

; Check that we look through cast and recognize min idiom.

define zeroext i8 @look_through_cast1(i32 %x) {
; CHECK-LABEL: @look_through_cast1(
; CHECK-NEXT:    [[TMP1:%.*]] = icmp slt i32 [[X:%.*]], 511
; CHECK-NEXT:    [[RES1:%.*]] = select i1 [[TMP1]], i32 [[X]], i32 511
; CHECK-NEXT:    [[TMP2:%.*]] = trunc i32 [[RES1]] to i8
; CHECK-NEXT:    ret i8 [[TMP2]]
;
  %cmp1 = icmp slt i32 %x, 511
  %x_trunc = trunc i32 %x to i8
  %res = select i1 %cmp1, i8 %x_trunc, i8 255
  ret i8 %res
}

; Check that we look through cast but min is not recognized.

define zeroext i8 @look_through_cast2(i32 %x) {
; CHECK-LABEL: @look_through_cast2(
; CHECK-NEXT:    [[CMP1:%.*]] = icmp slt i32 [[X:%.*]], 510
; CHECK-NEXT:    [[X_TRUNC:%.*]] = trunc i32 [[X]] to i8
; CHECK-NEXT:    [[RES:%.*]] = select i1 [[CMP1]], i8 [[X_TRUNC]], i8 -1
; CHECK-NEXT:    ret i8 [[RES]]
;
  %cmp1 = icmp slt i32 %x, 510
  %x_trunc = trunc i32 %x to i8
  %res = select i1 %cmp1, i8 %x_trunc, i8 255
  ret i8 %res
}

define <2 x i8> @min_through_cast_vec1(<2 x i32> %x) {
; CHECK-LABEL: @min_through_cast_vec1(
; CHECK-NEXT:    [[TMP1:%.*]] = icmp slt <2 x i32> [[X:%.*]], <i32 510, i32 511>
; CHECK-NEXT:    [[RES1:%.*]] = select <2 x i1> [[TMP1]], <2 x i32> [[X]], <2 x i32> <i32 510, i32 511>
; CHECK-NEXT:    [[TMP2:%.*]] = trunc <2 x i32> [[RES1]] to <2 x i8>
; CHECK-NEXT:    ret <2 x i8> [[TMP2]]
;
  %cmp = icmp slt <2 x i32> %x, <i32 510, i32 511>
  %x_trunc = trunc <2 x i32> %x to <2 x i8>
  %res = select <2 x i1> %cmp, <2 x i8> %x_trunc, <2 x i8> <i8 254, i8 255>
  ret <2 x i8> %res
}

define <2 x i8> @min_through_cast_vec2(<2 x i32> %x) {
; CHECK-LABEL: @min_through_cast_vec2(
; CHECK-NEXT:    [[TMP1:%.*]] = icmp slt <2 x i32> [[X:%.*]], <i32 511, i32 511>
; CHECK-NEXT:    [[RES1:%.*]] = select <2 x i1> [[TMP1]], <2 x i32> [[X]], <2 x i32> <i32 511, i32 511>
; CHECK-NEXT:    [[TMP2:%.*]] = trunc <2 x i32> [[RES1]] to <2 x i8>
; CHECK-NEXT:    ret <2 x i8> [[TMP2]]
;
  %cmp = icmp slt <2 x i32> %x, <i32 511, i32 511>
  %x_trunc = trunc <2 x i32> %x to <2 x i8>
  %res = select <2 x i1> %cmp, <2 x i8> %x_trunc, <2 x i8> <i8 255, i8 255>
  ret <2 x i8> %res
}

; Remove a min/max op in a sequence with a common operand.
; PR35717: https://bugs.llvm.org/show_bug.cgi?id=35717

; min(min(a, b), min(b, c)) --> min(min(a, b), c)

define i32 @common_factor_smin(i32 %a, i32 %b, i32 %c) {
; CHECK-LABEL: @common_factor_smin(
; CHECK-NEXT:    [[CMP_AB:%.*]] = icmp slt i32 %a, %b
; CHECK-NEXT:    [[MIN_AB:%.*]] = select i1 [[CMP_AB]], i32 %a, i32 %b
; CHECK-NEXT:    [[TMP1:%.*]] = icmp slt i32 [[MIN_AB]], %c
; CHECK-NEXT:    [[MIN_ABC:%.*]] = select i1 [[TMP1]], i32 [[MIN_AB]], i32 %c
; CHECK-NEXT:    ret i32 [[MIN_ABC]]
;
  %cmp_ab = icmp slt i32 %a, %b
  %min_ab = select i1 %cmp_ab, i32 %a, i32 %b
  %cmp_bc = icmp slt i32 %b, %c
  %min_bc = select i1 %cmp_bc, i32 %b, i32 %c
  %cmp_ab_bc = icmp slt i32 %min_ab, %min_bc
  %min_abc = select i1 %cmp_ab_bc, i32 %min_ab, i32 %min_bc
  ret i32 %min_abc
}

; max(max(a, b), max(c, b)) --> max(max(a, b), c)

define <2 x i32> @common_factor_smax(<2 x i32> %a, <2 x i32> %b, <2 x i32> %c) {
; CHECK-LABEL: @common_factor_smax(
; CHECK-NEXT:    [[CMP_AB:%.*]] = icmp sgt <2 x i32> %a, %b
; CHECK-NEXT:    [[MAX_AB:%.*]] = select <2 x i1> [[CMP_AB]], <2 x i32> %a, <2 x i32> %b
; CHECK-NEXT:    [[TMP1:%.*]] = icmp sgt <2 x i32> [[MAX_AB]], %c
; CHECK-NEXT:    [[MAX_ABC:%.*]] = select <2 x i1> [[TMP1]], <2 x i32> [[MAX_AB]], <2 x i32> %c
; CHECK-NEXT:    ret <2 x i32> [[MAX_ABC]]
;
  %cmp_ab = icmp sgt <2 x i32> %a, %b
  %max_ab = select <2 x i1> %cmp_ab, <2 x i32> %a, <2 x i32> %b
  %cmp_cb = icmp sgt <2 x i32> %c, %b
  %max_cb = select <2 x i1> %cmp_cb, <2 x i32> %c, <2 x i32> %b
  %cmp_ab_cb = icmp sgt <2 x i32> %max_ab, %max_cb
  %max_abc = select <2 x i1> %cmp_ab_cb, <2 x i32> %max_ab, <2 x i32> %max_cb
  ret <2 x i32> %max_abc
}

; min(min(b, c), min(a, b)) --> min(min(b, c), a)

define <2 x i32> @common_factor_umin(<2 x i32> %a, <2 x i32> %b, <2 x i32> %c) {
; CHECK-LABEL: @common_factor_umin(
; CHECK-NEXT:    [[CMP_BC:%.*]] = icmp ult <2 x i32> %b, %c
; CHECK-NEXT:    [[MIN_BC:%.*]] = select <2 x i1> [[CMP_BC]], <2 x i32> %b, <2 x i32> %c
; CHECK-NEXT:    [[TMP1:%.*]] = icmp ult <2 x i32> [[MIN_BC]], %a
; CHECK-NEXT:    [[MIN_ABC:%.*]] = select <2 x i1> [[TMP1]], <2 x i32> [[MIN_BC]], <2 x i32> %a
; CHECK-NEXT:    ret <2 x i32> [[MIN_ABC]]
;
  %cmp_bc = icmp ult <2 x i32> %b, %c
  %min_bc = select <2 x i1> %cmp_bc, <2 x i32> %b, <2 x i32> %c
  %cmp_ab = icmp ult <2 x i32> %a, %b
  %min_ab = select <2 x i1> %cmp_ab, <2 x i32> %a, <2 x i32> %b
  %cmp_bc_ab = icmp ult <2 x i32> %min_bc, %min_ab
  %min_abc = select <2 x i1> %cmp_bc_ab, <2 x i32> %min_bc, <2 x i32> %min_ab
  ret <2 x i32> %min_abc
}

; max(max(b, c), max(b, a)) --> max(max(b, c), a)

define i32 @common_factor_umax(i32 %a, i32 %b, i32 %c) {
; CHECK-LABEL: @common_factor_umax(
; CHECK-NEXT:    [[CMP_BC:%.*]] = icmp ugt i32 %b, %c
; CHECK-NEXT:    [[MAX_BC:%.*]] = select i1 [[CMP_BC]], i32 %b, i32 %c
; CHECK-NEXT:    [[TMP1:%.*]] = icmp ugt i32 [[MAX_BC]], %a
; CHECK-NEXT:    [[MAX_ABC:%.*]] = select i1 [[TMP1]], i32 [[MAX_BC]], i32 %a
; CHECK-NEXT:    ret i32 [[MAX_ABC]]
;
  %cmp_bc = icmp ugt i32 %b, %c
  %max_bc = select i1 %cmp_bc, i32 %b, i32 %c
  %cmp_ba = icmp ugt i32 %b, %a
  %max_ba = select i1 %cmp_ba, i32 %b, i32 %a
  %cmp_bc_ba = icmp ugt i32 %max_bc, %max_ba
  %max_abc = select i1 %cmp_bc_ba, i32 %max_bc, i32 %max_ba
  ret i32 %max_abc
}

declare void @extra_use(i32)

define i32 @common_factor_umax_extra_use_lhs(i32 %a, i32 %b, i32 %c) {
; CHECK-LABEL: @common_factor_umax_extra_use_lhs(
; CHECK-NEXT:    [[CMP_BC:%.*]] = icmp ugt i32 %b, %c
; CHECK-NEXT:    [[MAX_BC:%.*]] = select i1 [[CMP_BC]], i32 %b, i32 %c
; CHECK-NEXT:    [[TMP1:%.*]] = icmp ugt i32 [[MAX_BC]], %a
; CHECK-NEXT:    [[MAX_ABC:%.*]] = select i1 [[TMP1]], i32 [[MAX_BC]], i32 %a
; CHECK-NEXT:    call void @extra_use(i32 [[MAX_BC]])
; CHECK-NEXT:    ret i32 [[MAX_ABC]]
;
  %cmp_bc = icmp ugt i32 %b, %c
  %max_bc = select i1 %cmp_bc, i32 %b, i32 %c
  %cmp_ba = icmp ugt i32 %b, %a
  %max_ba = select i1 %cmp_ba, i32 %b, i32 %a
  %cmp_bc_ba = icmp ugt i32 %max_bc, %max_ba
  %max_abc = select i1 %cmp_bc_ba, i32 %max_bc, i32 %max_ba
  call void @extra_use(i32 %max_bc)
  ret i32 %max_abc
}

define i32 @common_factor_umax_extra_use_rhs(i32 %a, i32 %b, i32 %c) {
; CHECK-LABEL: @common_factor_umax_extra_use_rhs(
; CHECK-NEXT:    [[CMP_BA:%.*]] = icmp ugt i32 %b, %a
; CHECK-NEXT:    [[MAX_BA:%.*]] = select i1 [[CMP_BA]], i32 %b, i32 %a
; CHECK-NEXT:    [[TMP1:%.*]] = icmp ugt i32 [[MAX_BA]], %c
; CHECK-NEXT:    [[MAX_ABC:%.*]] = select i1 [[TMP1]], i32 [[MAX_BA]], i32 %c
; CHECK-NEXT:    call void @extra_use(i32 [[MAX_BA]])
; CHECK-NEXT:    ret i32 [[MAX_ABC]]
;
  %cmp_bc = icmp ugt i32 %b, %c
  %max_bc = select i1 %cmp_bc, i32 %b, i32 %c
  %cmp_ba = icmp ugt i32 %b, %a
  %max_ba = select i1 %cmp_ba, i32 %b, i32 %a
  %cmp_bc_ba = icmp ugt i32 %max_bc, %max_ba
  %max_abc = select i1 %cmp_bc_ba, i32 %max_bc, i32 %max_ba
  call void @extra_use(i32 %max_ba)
  ret i32 %max_abc
}

define i32 @common_factor_umax_extra_use_both(i32 %a, i32 %b, i32 %c) {
; CHECK-LABEL: @common_factor_umax_extra_use_both(
; CHECK-NEXT:    [[CMP_BC:%.*]] = icmp ugt i32 %b, %c
; CHECK-NEXT:    [[MAX_BC:%.*]] = select i1 [[CMP_BC]], i32 %b, i32 %c
; CHECK-NEXT:    [[CMP_BA:%.*]] = icmp ugt i32 %b, %a
; CHECK-NEXT:    [[MAX_BA:%.*]] = select i1 [[CMP_BA]], i32 %b, i32 %a
; CHECK-NEXT:    [[CMP_BC_BA:%.*]] = icmp ugt i32 [[MAX_BC]], [[MAX_BA]]
; CHECK-NEXT:    [[MAX_ABC:%.*]] = select i1 [[CMP_BC_BA]], i32 [[MAX_BC]], i32 [[MAX_BA]]
; CHECK-NEXT:    call void @extra_use(i32 [[MAX_BC]])
; CHECK-NEXT:    call void @extra_use(i32 [[MAX_BA]])
; CHECK-NEXT:    ret i32 [[MAX_ABC]]
;
  %cmp_bc = icmp ugt i32 %b, %c
  %max_bc = select i1 %cmp_bc, i32 %b, i32 %c
  %cmp_ba = icmp ugt i32 %b, %a
  %max_ba = select i1 %cmp_ba, i32 %b, i32 %a
  %cmp_bc_ba = icmp ugt i32 %max_bc, %max_ba
  %max_abc = select i1 %cmp_bc_ba, i32 %max_bc, i32 %max_ba
  call void @extra_use(i32 %max_bc)
  call void @extra_use(i32 %max_ba)
  ret i32 %max_abc
}

; This would assert. Don't assume that earlier min/max types match a possible later min/max.

define float @not_min_of_min(i8 %i, float %x) {
; CHECK-LABEL: @not_min_of_min(
; CHECK-NEXT:    [[CMP1_INV:%.*]] = fcmp fast oge float [[X:%.*]], 1.000000e+00
; CHECK-NEXT:    [[MIN1:%.*]] = select i1 [[CMP1_INV]], float 1.000000e+00, float [[X]]
; CHECK-NEXT:    [[CMP2_INV:%.*]] = fcmp fast oge float [[X]], 2.000000e+00
; CHECK-NEXT:    [[MIN2:%.*]] = select i1 [[CMP2_INV]], float 2.000000e+00, float [[X]]
; CHECK-NEXT:    [[CMP3:%.*]] = icmp ult i8 [[I:%.*]], 16
; CHECK-NEXT:    [[R:%.*]] = select i1 [[CMP3]], float [[MIN1]], float [[MIN2]]
; CHECK-NEXT:    ret float [[R]]
;
  %cmp1 = fcmp fast ult float %x, 1.0
  %min1 = select i1 %cmp1, float %x, float 1.0
  %cmp2 = fcmp fast ult float %x, 2.0
  %min2 = select i1 %cmp2, float %x, float 2.0
  %cmp3 = icmp ult i8 %i, 16
  %r = select i1 %cmp3, float %min1, float %min2
  ret float %r
}


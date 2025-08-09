  $ tc=../src/main.exe
  $ clang=clang-18
  $ compile() {
  >   echo; echo "*** BEGIN $1 ***"; echo
  >   cat $1; echo
  >   if $tc -dllvm -O0 $1; then
  >     if $clang ${1%.tig}.bc ../runtime/runtime.c -o ${1%.tig}.exe; then
  >       echo; echo "*** OUTPUT ***"
  >       ./${1%.tig}.exe
  >     fi
  >   fi
  >   echo; echo "*** END $1 ***"; echo
  > }
  $ for t in *.tig; do compile $t; done
  
  *** BEGIN test001.tig ***
  
  let var x := 12 var y := x + x in printi(y) end
  
  
  define void @TIG_main() gc "shadow-stack" {
  entry:
    %0 = alloca i64, align 8
    %1 = alloca i64, align 8
    store i64 12, ptr %1, align 4
    %2 = load i64, ptr %1, align 4
    %3 = load i64, ptr %1, align 4
    %4 = add i64 %2, %3
    store i64 %4, ptr %0, align 4
    %5 = load i64, ptr %0, align 4
    call void @TIG_printi(i64 %5)
    ret void
  }
  
  declare void @TIG_printi(i64 %0)
  warning: overriding the module target triple with x86_64-pc-linux-gnu [-Woverride-module]
  1 warning generated.
  
  *** OUTPUT ***
  24
  *** END test001.tig ***
  
  
  *** BEGIN test002.tig ***
  
  let
    type t = int
    var x : t := 42
  in
    printi(x)
  end
  
  define void @TIG_main() gc "shadow-stack" {
  entry:
    %0 = alloca i64, align 8
    store i64 42, ptr %0, align 4
    %1 = load i64, ptr %0, align 4
    call void @TIG_printi(i64 %1)
    ret void
  }
  
  declare void @TIG_printi(i64 %0)
  warning: overriding the module target triple with x86_64-pc-linux-gnu [-Woverride-module]
  1 warning generated.
  
  *** OUTPUT ***
  42
  *** END test002.tig ***
  
  
  *** BEGIN test003.tig ***
  
  let
    var N := 100
    var x0 := 0
    var x1 := 1
  in
    for i := 1 to N do
      (let var x2 := x0 + x1 in x0 := x1; x1 := x2 end);
    printi(x1)
  end
  
  define void @TIG_main() gc "shadow-stack" {
  entry:
    %0 = alloca i64, align 8
    %1 = alloca i64, align 8
    %2 = alloca i64, align 8
    %3 = alloca i64, align 8
    %4 = alloca i64, align 8
    store i64 100, ptr %2, align 4
    store i64 0, ptr %3, align 4
    store i64 1, ptr %0, align 4
    store i64 1, ptr %1, align 4
    br label %5
  
  5:                                                ; preds = %entry, %22
    %6 = load i64, ptr %2, align 4
    %7 = load i64, ptr %1, align 4
    %8 = icmp slt i64 %6, %7
    %9 = zext i1 %8 to i64
    %10 = icmp ne i64 %9, 0
    br i1 %10, label %11, label %14
  
  11:                                               ; preds = %5
    br label %12
  
  12:                                               ; preds = %11
    %13 = load i64, ptr %0, align 4
    call void @TIG_printi(i64 %13)
    ret void
  
  14:                                               ; preds = %5
    %15 = load i64, ptr %3, align 4
    %16 = load i64, ptr %0, align 4
    %17 = add i64 %15, %16
    store i64 %17, ptr %4, align 4
    %18 = load i64, ptr %0, align 4
    store i64 %18, ptr %3, align 4
    %19 = load i64, ptr %4, align 4
    store i64 %19, ptr %0, align 4
    %20 = load i64, ptr %1, align 4
    %21 = add i64 %20, 1
    store i64 %21, ptr %1, align 4
    br label %22
  
  22:                                               ; preds = %14
    br label %5
  }
  
  declare void @TIG_printi(i64 %0)
  warning: overriding the module target triple with x86_64-pc-linux-gnu [-Woverride-module]
  1 warning generated.
  
  *** OUTPUT ***
  -1869596475
  *** END test003.tig ***
  
  
  *** BEGIN test004.tig ***
  
  let
    var x := 0
    var y := 1
  in
    y := x
  end
  
  define void @TIG_main() gc "shadow-stack" {
  entry:
    %0 = alloca i64, align 8
    %1 = alloca i64, align 8
    store i64 0, ptr %1, align 4
    store i64 1, ptr %0, align 4
    %2 = load i64, ptr %1, align 4
    store i64 %2, ptr %0, align 4
    ret void
  }
  warning: overriding the module target triple with x86_64-pc-linux-gnu [-Woverride-module]
  1 warning generated.
  
  *** OUTPUT ***
  
  *** END test004.tig ***
  
  
  *** BEGIN test005.tig ***
  
  let
    var x := 42
  in
    if x > 12 then x := 0
  end
  
  define void @TIG_main() gc "shadow-stack" {
  entry:
    %0 = alloca i64, align 8
    store i64 42, ptr %0, align 4
    %1 = load i64, ptr %0, align 4
    %2 = icmp sgt i64 %1, 12
    %3 = zext i1 %2 to i64
    %4 = icmp ne i64 %3, 0
    br i1 %4, label %5, label %7
  
  5:                                                ; preds = %entry
    store i64 0, ptr %0, align 4
    br label %6
  
  6:                                                ; preds = %7, %5
    ret void
  
  7:                                                ; preds = %entry
    br label %6
  }
  warning: overriding the module target triple with x86_64-pc-linux-gnu [-Woverride-module]
  1 warning generated.
  
  *** OUTPUT ***
  
  *** END test005.tig ***
  
  
  *** BEGIN test006.tig ***
  
  let
    type t = array of int
    var x := t [10] of 42
  in
    printi(x[3])
  end
  
  
  define void @TIG_main() gc "shadow-stack" {
  entry:
    %0 = alloca ptr, align 8
    store ptr null, ptr %0, align 8
    call void @llvm.gcroot(ptr %0, ptr null)
    %1 = alloca ptr, align 8
    store ptr null, ptr %1, align 8
    call void @llvm.gcroot(ptr %1, ptr null)
    %2 = call ptr @TIG_makeintarray(i64 10, i64 42)
    store ptr %2, ptr %1, align 8
    %3 = load ptr, ptr %1, align 8
    store ptr %3, ptr %0, align 8
    %4 = load ptr, ptr %0, align 8
    %5 = getelementptr i64, ptr %4, i64 3
    %6 = load i64, ptr %5, align 4
    call void @TIG_printi(i64 %6)
    ret void
  }
  
  ; Function Attrs: nounwind
  declare void @llvm.gcroot(ptr %0, ptr %1) #0
  
  declare ptr @TIG_makeintarray(i64 %0, i64 %1)
  
  declare void @TIG_printi(i64 %0)
  
  attributes #0 = { nounwind }
  warning: overriding the module target triple with x86_64-pc-linux-gnu [-Woverride-module]
  1 warning generated.
  
  *** OUTPUT ***
  42
  *** END test006.tig ***
  
  
  *** BEGIN test007.tig ***
  
  let
    type t = array of int
    var N := 500
    var x := t [N+1] of 1
  in
    print("PRIMES AT MOST "); printi(N); print("\n");
    for i := 2 to N do (
      if x[i] then (
        printi(i); print(" ");
        for k := i to N/i do x[i*k] := 0
      )
    );
    print("\n")
  end
  
  @0 = private unnamed_addr constant [16 x i8] c"PRIMES AT MOST \00", align 1
  @1 = private unnamed_addr constant [2 x i8] c"\0A\00", align 1
  @2 = private unnamed_addr constant [2 x i8] c" \00", align 1
  
  define void @TIG_main() gc "shadow-stack" {
  entry:
    %0 = alloca i64, align 8
    %1 = alloca ptr, align 8
    store ptr null, ptr %1, align 8
    call void @llvm.gcroot(ptr %1, ptr null)
    %2 = alloca i64, align 8
    %3 = alloca ptr, align 8
    store ptr null, ptr %3, align 8
    call void @llvm.gcroot(ptr %3, ptr null)
    %4 = alloca i64, align 8
    store i64 500, ptr %0, align 4
    %5 = load i64, ptr %0, align 4
    %6 = add i64 %5, 1
    %7 = call ptr @TIG_makeintarray(i64 %6, i64 1)
    store ptr %7, ptr %1, align 8
    %8 = load ptr, ptr %1, align 8
    store ptr %8, ptr %3, align 8
    call void @TIG_print(ptr @0)
    %9 = load i64, ptr %0, align 4
    call void @TIG_printi(i64 %9)
    call void @TIG_print(ptr @1)
    store i64 2, ptr %4, align 4
    br label %10
  
  10:                                               ; preds = %entry, %40
    %11 = load i64, ptr %0, align 4
    %12 = load i64, ptr %4, align 4
    %13 = icmp slt i64 %11, %12
    %14 = zext i1 %13 to i64
    %15 = icmp ne i64 %14, 0
    br i1 %15, label %16, label %18
  
  16:                                               ; preds = %10
    br label %17
  
  17:                                               ; preds = %16
    call void @TIG_print(ptr @1)
    ret void
  
  18:                                               ; preds = %10
    %19 = load i64, ptr %4, align 4
    %20 = load ptr, ptr %3, align 8
    %21 = getelementptr i64, ptr %20, i64 %19
    %22 = load i64, ptr %21, align 4
    %23 = icmp ne i64 %22, 0
    br i1 %23, label %24, label %50
  
  24:                                               ; preds = %18
    %25 = load i64, ptr %4, align 4
    call void @TIG_printi(i64 %25)
    call void @TIG_print(ptr @2)
    %26 = load i64, ptr %4, align 4
    store i64 %26, ptr %2, align 4
    br label %27
  
  27:                                               ; preds = %24, %49
    %28 = load i64, ptr %0, align 4
    %29 = load i64, ptr %4, align 4
    %30 = sdiv i64 %28, %29
    %31 = load i64, ptr %2, align 4
    %32 = icmp slt i64 %30, %31
    %33 = zext i1 %32 to i64
    %34 = icmp ne i64 %33, 0
    br i1 %34, label %35, label %41
  
  35:                                               ; preds = %27
    br label %36
  
  36:                                               ; preds = %35
    br label %37
  
  37:                                               ; preds = %50, %36
    %38 = load i64, ptr %4, align 4
    %39 = add i64 %38, 1
    store i64 %39, ptr %4, align 4
    br label %40
  
  40:                                               ; preds = %37
    br label %10
  
  41:                                               ; preds = %27
    %42 = load i64, ptr %4, align 4
    %43 = load i64, ptr %2, align 4
    %44 = mul i64 %42, %43
    %45 = load ptr, ptr %3, align 8
    %46 = getelementptr i64, ptr %45, i64 %44
    store i64 0, ptr %46, align 4
    %47 = load i64, ptr %2, align 4
    %48 = add i64 %47, 1
    store i64 %48, ptr %2, align 4
    br label %49
  
  49:                                               ; preds = %41
    br label %27
  
  50:                                               ; preds = %18
    br label %37
  }
  
  ; Function Attrs: nounwind
  declare void @llvm.gcroot(ptr %0, ptr %1) #0
  
  declare ptr @TIG_makeintarray(i64 %0, i64 %1)
  
  declare void @TIG_print(ptr %0)
  
  declare void @TIG_printi(i64 %0)
  
  attributes #0 = { nounwind }
  warning: overriding the module target triple with x86_64-pc-linux-gnu [-Woverride-module]
  1 warning generated.
  
  *** OUTPUT ***
  PRIMES AT MOST 500
  2 3 5 7 11 13 17 19 23 29 31 37 41 43 47 53 59 61 67 71 73 79 83 89 97 101 103 107 109 113 127 131 137 139 149 151 157 163 167 173 179 181 191 193 197 199 211 223 227 229 233 239 241 251 257 263 269 271 277 281 283 293 307 311 313 317 331 337 347 349 353 359 367 373 379 383 389 397 401 409 419 421 431 433 439 443 449 457 461 463 467 479 487 491 499 
  
  *** END test007.tig ***
  
  
  *** BEGIN test008.tig ***
  
  print("Hello, World!\n")
  
  @0 = private unnamed_addr constant [15 x i8] c"Hello, World!\0A\00", align 1
  
  define void @TIG_main() gc "shadow-stack" {
  entry:
    call void @TIG_print(ptr @0)
    ret void
  }
  
  declare void @TIG_print(ptr %0)
  warning: overriding the module target triple with x86_64-pc-linux-gnu [-Woverride-module]
  1 warning generated.
  
  *** OUTPUT ***
  Hello, World!
  
  *** END test008.tig ***
  
  
  *** BEGIN test009.tig ***
  
  let
    type list = { hd: int, tl: list }
    var x := list { hd = 42, tl = list { hd = 12, tl = nil } }
  in
    printi(x.tl.hd)
  end
  
  
  @0 = private unnamed_addr constant [12 x i8] c"test009.tig\00", align 1
  
  define void @TIG_main() gc "shadow-stack" {
  entry:
    %0 = alloca ptr, align 8
    store ptr null, ptr %0, align 8
    call void @llvm.gcroot(ptr %0, ptr null)
    %1 = alloca ptr, align 8
    store ptr null, ptr %1, align 8
    call void @llvm.gcroot(ptr %1, ptr null)
    %2 = alloca ptr, align 8
    store ptr null, ptr %2, align 8
    call void @llvm.gcroot(ptr %2, ptr null)
    %3 = call ptr @TIG_makerecord(i32 2)
    %4 = getelementptr { i64, ptr }, ptr %3, i64 0, i64 0
    store i64 12, ptr %4, align 4
    %5 = getelementptr { i64, ptr }, ptr %3, i64 0, i64 1
    store ptr null, ptr %5, align 8
    store ptr %3, ptr %0, align 8
    %6 = call ptr @TIG_makerecord(i32 2)
    %7 = load ptr, ptr %0, align 8
    %8 = getelementptr { i64, ptr }, ptr %6, i64 0, i64 0
    store i64 42, ptr %8, align 4
    %9 = getelementptr { i64, ptr }, ptr %6, i64 0, i64 1
    store ptr %7, ptr %9, align 8
    store ptr %6, ptr %1, align 8
    %10 = load ptr, ptr %1, align 8
    store ptr %10, ptr %2, align 8
    %11 = load ptr, ptr %2, align 8
    %12 = icmp eq ptr %11, null
    br i1 %12, label %13, label %14
  
  13:                                               ; preds = %entry
    call void @TIG_nil_error(ptr @0, i64 5, i64 10)
    unreachable
  
  14:                                               ; preds = %entry
    %15 = getelementptr { i64, ptr }, ptr %11, i64 0, i64 1
    %16 = load ptr, ptr %15, align 8
    %17 = icmp eq ptr %16, null
    br i1 %17, label %18, label %19
  
  18:                                               ; preds = %14
    call void @TIG_nil_error(ptr @0, i64 5, i64 10)
    unreachable
  
  19:                                               ; preds = %14
    %20 = getelementptr { i64, ptr }, ptr %16, i64 0, i64 0
    %21 = load i64, ptr %20, align 4
    call void @TIG_printi(i64 %21)
    ret void
  }
  
  ; Function Attrs: nounwind
  declare void @llvm.gcroot(ptr %0, ptr %1) #0
  
  declare ptr @TIG_makerecord(i32 %0)
  
  declare void @TIG_nil_error(ptr %0, i64 %1, i64 %2)
  
  declare void @TIG_printi(i64 %0)
  
  attributes #0 = { nounwind }
  warning: overriding the module target triple with x86_64-pc-linux-gnu [-Woverride-module]
  1 warning generated.
  
  *** OUTPUT ***
  # GC roots: 3
  # GC roots: 3
  12
  *** END test009.tig ***
  
  
  *** BEGIN test010.tig ***
  
  let
    type list = { hd: int, tl: list }
    var x : list := nil
  in
    printi(x.hd)
  end
  
  
  @0 = private unnamed_addr constant [12 x i8] c"test010.tig\00", align 1
  
  define void @TIG_main() gc "shadow-stack" {
  entry:
    %0 = alloca ptr, align 8
    store ptr null, ptr %0, align 8
    call void @llvm.gcroot(ptr %0, ptr null)
    store ptr null, ptr %0, align 8
    %1 = load ptr, ptr %0, align 8
    %2 = icmp eq ptr %1, null
    br i1 %2, label %3, label %4
  
  3:                                                ; preds = %entry
    call void @TIG_nil_error(ptr @0, i64 5, i64 10)
    unreachable
  
  4:                                                ; preds = %entry
    %5 = getelementptr { i64, ptr }, ptr %1, i64 0, i64 0
    %6 = load i64, ptr %5, align 4
    call void @TIG_printi(i64 %6)
    ret void
  }
  
  ; Function Attrs: nounwind
  declare void @llvm.gcroot(ptr %0, ptr %1) #0
  
  declare void @TIG_nil_error(ptr %0, i64 %1, i64 %2)
  
  declare void @TIG_printi(i64 %0)
  
  attributes #0 = { nounwind }
  warning: overriding the module target triple with x86_64-pc-linux-gnu [-Woverride-module]
  1 warning generated.
  
  *** OUTPUT ***
  test010.tig:5:10: variable is nil
  
  *** END test010.tig ***
  
  
  *** BEGIN test011.tig ***
  
  let
    type rec = { a : int, b : rec }
    type arr = array of rec
    var a := arr[10] of nil
  in
    a[3] := nil
  end
  
  
  define void @TIG_main() gc "shadow-stack" {
  entry:
    %0 = alloca ptr, align 8
    store ptr null, ptr %0, align 8
    call void @llvm.gcroot(ptr %0, ptr null)
    %1 = alloca ptr, align 8
    store ptr null, ptr %1, align 8
    call void @llvm.gcroot(ptr %1, ptr null)
    %2 = call ptr @TIG_makeptrarray(i64 10, ptr null)
    store ptr %2, ptr %0, align 8
    %3 = load ptr, ptr %0, align 8
    store ptr %3, ptr %1, align 8
    %4 = load ptr, ptr %1, align 8
    %5 = getelementptr ptr, ptr %4, i64 3
    store ptr null, ptr %5, align 8
    ret void
  }
  
  ; Function Attrs: nounwind
  declare void @llvm.gcroot(ptr %0, ptr %1) #0
  
  declare ptr @TIG_makeptrarray(i64 %0, ptr %1)
  
  attributes #0 = { nounwind }
  warning: overriding the module target triple with x86_64-pc-linux-gnu [-Woverride-module]
  1 warning generated.
  /usr/bin/ld: /tmp/build_98e354_dune/test011-8fb2ac.o: in function `TIG_main':
  :(.text+0x56): undefined reference to `TIG_makeptrarray'
  clang-18: error: linker command failed with exit code 1 (use -v to see invocation)
  
  *** END test011.tig ***
  
  
  *** BEGIN test012.tig ***
  
  let
    type arr0 = array of int
    type arr1 = array of arr0
    var a := arr1[10] of (arr0[43] of 3)
  in
    a[3][5] := 123;
    printi(a[3][5])
  end
  
  
  define void @TIG_main() gc "shadow-stack" {
  entry:
    %0 = alloca ptr, align 8
    store ptr null, ptr %0, align 8
    call void @llvm.gcroot(ptr %0, ptr null)
    %1 = alloca ptr, align 8
    store ptr null, ptr %1, align 8
    call void @llvm.gcroot(ptr %1, ptr null)
    %2 = alloca ptr, align 8
    store ptr null, ptr %2, align 8
    call void @llvm.gcroot(ptr %2, ptr null)
    %3 = call ptr @TIG_makeintarray(i64 43, i64 3)
    store ptr %3, ptr %1, align 8
    %4 = load ptr, ptr %1, align 8
    %5 = call ptr @TIG_makeptrarray(i64 10, ptr %4)
    store ptr %5, ptr %0, align 8
    %6 = load ptr, ptr %0, align 8
    store ptr %6, ptr %2, align 8
    %7 = load ptr, ptr %2, align 8
    %8 = getelementptr ptr, ptr %7, i64 3
    %9 = load ptr, ptr %8, align 8
    %10 = getelementptr i64, ptr %9, i64 5
    store i64 123, ptr %10, align 4
    %11 = load ptr, ptr %2, align 8
    %12 = getelementptr ptr, ptr %11, i64 3
    %13 = load ptr, ptr %12, align 8
    %14 = getelementptr i64, ptr %13, i64 5
    %15 = load i64, ptr %14, align 4
    call void @TIG_printi(i64 %15)
    ret void
  }
  
  ; Function Attrs: nounwind
  declare void @llvm.gcroot(ptr %0, ptr %1) #0
  
  declare ptr @TIG_makeintarray(i64 %0, i64 %1)
  
  declare ptr @TIG_makeptrarray(i64 %0, ptr %1)
  
  declare void @TIG_printi(i64 %0)
  
  attributes #0 = { nounwind }
  warning: overriding the module target triple with x86_64-pc-linux-gnu [-Woverride-module]
  1 warning generated.
  /usr/bin/ld: /tmp/build_98e354_dune/test012-afdcf0.o: in function `TIG_main':
  :(.text+0x8f): undefined reference to `TIG_makeptrarray'
  clang-18: error: linker command failed with exit code 1 (use -v to see invocation)
  
  *** END test012.tig ***
  
  
  *** BEGIN test013.tig ***
  
  let
    var N := 50
    type arr = array of int
    var a := arr[N] of 0
  in
    for i := 0 to N-1 do
      a[i] := i;
    for i := 0 to N-1 do (
      printi (a[i]); print ("\n")
    )
  end
  
  
  @0 = private unnamed_addr constant [2 x i8] c"\0A\00", align 1
  
  define void @TIG_main() gc "shadow-stack" {
  entry:
    %0 = alloca ptr, align 8
    store ptr null, ptr %0, align 8
    call void @llvm.gcroot(ptr %0, ptr null)
    %1 = alloca i64, align 8
    %2 = alloca ptr, align 8
    store ptr null, ptr %2, align 8
    call void @llvm.gcroot(ptr %2, ptr null)
    %3 = alloca i64, align 8
    %4 = alloca i64, align 8
    store i64 50, ptr %1, align 4
    %5 = load i64, ptr %1, align 4
    %6 = call ptr @TIG_makeintarray(i64 %5, i64 0)
    store ptr %6, ptr %0, align 8
    %7 = load ptr, ptr %0, align 8
    store ptr %7, ptr %2, align 8
    store i64 0, ptr %3, align 4
    br label %8
  
  8:                                                ; preds = %entry, %41
    %9 = load i64, ptr %1, align 4
    %10 = sub i64 %9, 1
    %11 = load i64, ptr %3, align 4
    %12 = icmp slt i64 %10, %11
    %13 = zext i1 %12 to i64
    %14 = icmp ne i64 %13, 0
    br i1 %14, label %15, label %34
  
  15:                                               ; preds = %8
    br label %16
  
  16:                                               ; preds = %15
    store i64 0, ptr %4, align 4
    br label %17
  
  17:                                               ; preds = %16, %33
    %18 = load i64, ptr %1, align 4
    %19 = sub i64 %18, 1
    %20 = load i64, ptr %4, align 4
    %21 = icmp slt i64 %19, %20
    %22 = zext i1 %21 to i64
    %23 = icmp ne i64 %22, 0
    br i1 %23, label %24, label %26
  
  24:                                               ; preds = %17
    br label %25
  
  25:                                               ; preds = %24
    ret void
  
  26:                                               ; preds = %17
    %27 = load i64, ptr %4, align 4
    %28 = load ptr, ptr %2, align 8
    %29 = getelementptr i64, ptr %28, i64 %27
    %30 = load i64, ptr %29, align 4
    call void @TIG_printi(i64 %30)
    call void @TIG_print(ptr @0)
    %31 = load i64, ptr %4, align 4
    %32 = add i64 %31, 1
    store i64 %32, ptr %4, align 4
    br label %33
  
  33:                                               ; preds = %26
    br label %17
  
  34:                                               ; preds = %8
    %35 = load i64, ptr %3, align 4
    %36 = load ptr, ptr %2, align 8
    %37 = getelementptr i64, ptr %36, i64 %35
    %38 = load i64, ptr %3, align 4
    store i64 %38, ptr %37, align 4
    %39 = load i64, ptr %3, align 4
    %40 = add i64 %39, 1
    store i64 %40, ptr %3, align 4
    br label %41
  
  41:                                               ; preds = %34
    br label %8
  }
  
  ; Function Attrs: nounwind
  declare void @llvm.gcroot(ptr %0, ptr %1) #0
  
  declare ptr @TIG_makeintarray(i64 %0, i64 %1)
  
  declare void @TIG_printi(i64 %0)
  
  declare void @TIG_print(ptr %0)
  
  attributes #0 = { nounwind }
  warning: overriding the module target triple with x86_64-pc-linux-gnu [-Woverride-module]
  1 warning generated.
  
  *** OUTPUT ***
  0
  1
  2
  3
  4
  5
  6
  7
  8
  9
  10
  11
  12
  13
  14
  15
  16
  17
  18
  19
  20
  21
  22
  23
  24
  25
  26
  27
  28
  29
  30
  31
  32
  33
  34
  35
  36
  37
  38
  39
  40
  41
  42
  43
  44
  45
  46
  47
  48
  49
  
  *** END test013.tig ***
  
  
  *** BEGIN test014.tig ***
  
  let
    var a := 34
  in
    while a do a := if a then (break; 1) else 3
  end
  
  
  
  define void @TIG_main() gc "shadow-stack" {
  entry:
    %0 = alloca i64, align 8
    %1 = alloca i64, align 8
    store i64 34, ptr %1, align 4
    br label %2
  
  2:                                                ; preds = %entry, %13
    %3 = load i64, ptr %1, align 4
    %4 = icmp ne i64 %3, 0
    br i1 %4, label %5, label %14
  
  5:                                                ; preds = %2
    %6 = load i64, ptr %1, align 4
    %7 = icmp ne i64 %6, 0
    br i1 %7, label %8, label %10
  
  8:                                                ; preds = %5
    br label %9
  
  9:                                                ; preds = %14, %8
    ret void
  
  10:                                               ; preds = %5
    store i64 3, ptr %0, align 4
    br label %11
  
  11:                                               ; preds = %10
    %12 = load i64, ptr %0, align 4
    store i64 %12, ptr %1, align 4
    br label %13
  
  13:                                               ; preds = %11
    br label %2
  
  14:                                               ; preds = %2
    br label %9
  }
  warning: overriding the module target triple with x86_64-pc-linux-gnu [-Woverride-module]
  1 warning generated.
  
  *** OUTPUT ***
  
  *** END test014.tig ***
  
  
  *** BEGIN test015.tig ***
  
  /* ERR: unknown variable */
  let
    var x := 42
  in
    printi(y)
  end
  
  error: test015.tig:5:10: unknown variable `y'
  
  *** END test015.tig ***
  
  
  *** BEGIN test016.tig ***
  
  /* ERR: unknown function */
  f(42)
  
  error: test016.tig:2:1: unknown function `f'
  
  *** END test016.tig ***
  
  
  *** BEGIN test017.tig ***
  
  /* ERR: unknown type name */
  t { hd = 42 }
  
  error: test017.tig:2:1: unknown type name `t'
  
  *** END test017.tig ***
  
  
  *** BEGIN test018.tig ***
  
  /* ERR: wrong arity */
  printi(42, 56)
  
  error: test018.tig:2:1: wrong number of arguments: expected 1, got 2
  
  *** END test018.tig ***
  
  
  *** BEGIN test019.tig ***
  
  /* ERR: repeated type name */
  let
    type t = string
    type t = int
  in
  end
  
  define void @TIG_main() gc "shadow-stack" {
  entry:
    ret void
  }
  warning: overriding the module target triple with x86_64-pc-linux-gnu [-Woverride-module]
  1 warning generated.
  
  *** OUTPUT ***
  
  *** END test019.tig ***
  
  
  *** BEGIN test020.tig ***
  
  /* ERR: statement expected */
  while 1 do
    43
  error: test020.tig:3:3: this expression should not produce a value
  
  *** END test020.tig ***
  
  
  *** BEGIN test021.tig ***
  
  /* ERR: not a record */
  let
    var x := 42
  in
    printi(x.r)
  end
  
  error: test021.tig:5:10: this expression does not belong to a record type
  
  *** END test021.tig ***
  
  
  *** BEGIN test022.tig ***
  
  /* ERR: not an array */
  let
    var x := 43
  in
    printi(x[18])
  end
  
  error: test022.tig:5:10: this expression does not belong to an array type
  
  *** END test022.tig ***
  
  
  *** BEGIN test023.tig ***
  
  /* ERR: unknown field */
  let
    type t = {x: int}
    var x : t := nil
  in
    printi(x.r)
  end
  
  error: test023.tig:6:12: record type `t' does not contain a field `r'
  
  *** END test023.tig ***
  
  
  *** BEGIN test024.tig ***
  
  /* ERR: illegal nil */
  let
    var x := nil
  in
  end
  
  error: test024.tig:3:12: `nil' cannot appear here
  
  *** END test024.tig ***
  
  
  *** BEGIN test025.tig ***
  
  /* Valid nil */
  let
    type t = { a : int }
    var x := t { a = 42 }
  in
    x := nil
  end
  
  
  define void @TIG_main() gc "shadow-stack" {
  entry:
    %0 = alloca ptr, align 8
    store ptr null, ptr %0, align 8
    call void @llvm.gcroot(ptr %0, ptr null)
    %1 = alloca ptr, align 8
    store ptr null, ptr %1, align 8
    call void @llvm.gcroot(ptr %1, ptr null)
    %2 = call ptr @TIG_makerecord(i32 1)
    %3 = getelementptr { i64 }, ptr %2, i64 0, i64 0
    store i64 42, ptr %3, align 4
    store ptr %2, ptr %1, align 8
    %4 = load ptr, ptr %1, align 8
    store ptr %4, ptr %0, align 8
    store ptr null, ptr %0, align 8
    ret void
  }
  
  ; Function Attrs: nounwind
  declare void @llvm.gcroot(ptr %0, ptr %1) #0
  
  declare ptr @TIG_makerecord(i32 %0)
  
  attributes #0 = { nounwind }
  warning: overriding the module target triple with x86_64-pc-linux-gnu [-Woverride-module]
  1 warning generated.
  
  *** OUTPUT ***
  # GC roots: 2
  
  *** END test025.tig ***
  
  
  *** BEGIN test026.tig ***
  
  /* ERR: illegal break */
  break
  error: test026.tig:2:1: `break' cannot appear here
  
  *** END test026.tig ***
  
  
  *** BEGIN test027.tig ***
  
  /* ERR: value expected */
  let
    var x := 42
    var y := (x := 0)
  in
  end
  
  error: test027.tig:4:12: value-producing expression was expected here
  
  *** END test027.tig ***
  
  
  *** BEGIN test028.tig ***
  
  /* ERR: Wrong number of fields */
  let
    type t = {a : int, b : string}
    var x := t{a = 42}
  in
  end
  
  error: test028.tig:4:12: some fields belonging to the type `t' are missing: b
  
  *** END test028.tig ***
  
  
  *** BEGIN test029.tig ***
  
  /* ERR: unexpected field */
  let
    type t = {a: int}
    var x := t{b = 42}
  in
  end
  
  error: test029.tig:4:14: a field named `a' belonging to the type `t' was expected here
  
  *** END test029.tig ***
  

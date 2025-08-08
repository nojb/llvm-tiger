  $ tc=../src/main.exe
  $ compile() {
  >   echo; echo "*** BEGIN $1 ***"; echo
  >   cat $1
  >   $tc -dllvm -O0 $1
  >   echo; echo "*** END $1 ***"; echo
  > }
  $ for t in *.tig; do compile $t; done
  
  *** BEGIN test1.tig ***
  
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
  
  *** END test1.tig ***
  
  
  *** BEGIN test10.tig ***
  
  let
    type list = { hd: int, tl: list }
    var x : list := nil
  in
    printi(x.hd)
  end
  
  @0 = private unnamed_addr constant [11 x i8] c"test10.tig\00", align 1
  
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
  
  *** END test10.tig ***
  
  
  *** BEGIN test2.tig ***
  
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
  
  *** END test2.tig ***
  
  
  *** BEGIN test3.tig ***
  
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
  
  *** END test3.tig ***
  
  
  *** BEGIN test4.tig ***
  
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
  
  *** END test4.tig ***
  
  
  *** BEGIN test5.tig ***
  
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
  
  *** END test5.tig ***
  
  
  *** BEGIN test6.tig ***
  
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
  
  *** END test6.tig ***
  
  
  *** BEGIN test7.tig ***
  
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
  
  *** END test7.tig ***
  
  
  *** BEGIN test8.tig ***
  
  print("Hello, World!\n")
  @0 = private unnamed_addr constant [15 x i8] c"Hello, World!\0A\00", align 1
  
  define void @TIG_main() gc "shadow-stack" {
  entry:
    call void @TIG_print(ptr @0)
    ret void
  }
  
  declare void @TIG_print(ptr %0)
  
  *** END test8.tig ***
  
  
  *** BEGIN test9.tig ***
  
  let
    type list = { hd: int, tl: list }
    var x := list { hd = 42, tl = list { hd = 12, tl = nil } }
  in
    printi(x.tl.hd)
  end
  
  @0 = private unnamed_addr constant [10 x i8] c"test9.tig\00", align 1
  
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
  
  *** END test9.tig ***
  

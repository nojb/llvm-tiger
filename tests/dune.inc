
(rule
 (targets test028.out.gen test028.err.gen)
 (action (run ../tools/run_test.exe -cmd %{dep:../src/main.exe} -runtime %{dep:../runtime/runtime.c} -out test028.out.gen -err test028.err.gen %{dep:test028.tig})))

(rule
 (alias runtest)
 (action (diff test028.out test028.out.gen)))

(rule
 (alias runtest)
 (action (diff test028.err test028.err.gen)))

(rule
 (targets test013.out.gen test013.err.gen)
 (action (run ../tools/run_test.exe -cmd %{dep:../src/main.exe} -runtime %{dep:../runtime/runtime.c} -out test013.out.gen -err test013.err.gen %{dep:test013.tig})))

(rule
 (alias runtest)
 (action (diff test013.out test013.out.gen)))

(rule
 (alias runtest)
 (action (diff test013.err test013.err.gen)))

(rule
 (targets test024.out.gen test024.err.gen)
 (action (run ../tools/run_test.exe -cmd %{dep:../src/main.exe} -runtime %{dep:../runtime/runtime.c} -out test024.out.gen -err test024.err.gen %{dep:test024.tig})))

(rule
 (alias runtest)
 (action (diff test024.out test024.out.gen)))

(rule
 (alias runtest)
 (action (diff test024.err test024.err.gen)))

(rule
 (targets test020.out.gen test020.err.gen)
 (action (run ../tools/run_test.exe -cmd %{dep:../src/main.exe} -runtime %{dep:../runtime/runtime.c} -out test020.out.gen -err test020.err.gen %{dep:test020.tig})))

(rule
 (alias runtest)
 (action (diff test020.out test020.out.gen)))

(rule
 (alias runtest)
 (action (diff test020.err test020.err.gen)))

(rule
 (targets test003.out.gen test003.err.gen)
 (action (run ../tools/run_test.exe -cmd %{dep:../src/main.exe} -runtime %{dep:../runtime/runtime.c} -out test003.out.gen -err test003.err.gen %{dep:test003.tig})))

(rule
 (alias runtest)
 (action (diff test003.out test003.out.gen)))

(rule
 (alias runtest)
 (action (diff test003.err test003.err.gen)))

(rule
 (targets test015.out.gen test015.err.gen)
 (action (run ../tools/run_test.exe -cmd %{dep:../src/main.exe} -runtime %{dep:../runtime/runtime.c} -out test015.out.gen -err test015.err.gen %{dep:test015.tig})))

(rule
 (alias runtest)
 (action (diff test015.out test015.out.gen)))

(rule
 (alias runtest)
 (action (diff test015.err test015.err.gen)))

(rule
 (targets test026.out.gen test026.err.gen)
 (action (run ../tools/run_test.exe -cmd %{dep:../src/main.exe} -runtime %{dep:../runtime/runtime.c} -out test026.out.gen -err test026.err.gen %{dep:test026.tig})))

(rule
 (alias runtest)
 (action (diff test026.out test026.out.gen)))

(rule
 (alias runtest)
 (action (diff test026.err test026.err.gen)))

(rule
 (targets test007.out.gen test007.err.gen)
 (action (run ../tools/run_test.exe -cmd %{dep:../src/main.exe} -runtime %{dep:../runtime/runtime.c} -out test007.out.gen -err test007.err.gen %{dep:test007.tig})))

(rule
 (alias runtest)
 (action (diff test007.out test007.out.gen)))

(rule
 (alias runtest)
 (action (diff test007.err test007.err.gen)))

(rule
 (targets test033.out.gen test033.err.gen)
 (action (run ../tools/run_test.exe -cmd %{dep:../src/main.exe} -runtime %{dep:../runtime/runtime.c} -out test033.out.gen -err test033.err.gen %{dep:test033.tig})))

(rule
 (alias runtest)
 (action (diff test033.out test033.out.gen)))

(rule
 (alias runtest)
 (action (diff test033.err test033.err.gen)))

(rule
 (targets test031.out.gen test031.err.gen)
 (action (run ../tools/run_test.exe -cmd %{dep:../src/main.exe} -runtime %{dep:../runtime/runtime.c} -out test031.out.gen -err test031.err.gen %{dep:test031.tig})))

(rule
 (alias runtest)
 (action (diff test031.out test031.out.gen)))

(rule
 (alias runtest)
 (action (diff test031.err test031.err.gen)))

(rule
 (targets test016.out.gen test016.err.gen)
 (action (run ../tools/run_test.exe -cmd %{dep:../src/main.exe} -runtime %{dep:../runtime/runtime.c} -out test016.out.gen -err test016.err.gen %{dep:test016.tig})))

(rule
 (alias runtest)
 (action (diff test016.out test016.out.gen)))

(rule
 (alias runtest)
 (action (diff test016.err test016.err.gen)))

(rule
 (targets test014.out.gen test014.err.gen)
 (action (run ../tools/run_test.exe -cmd %{dep:../src/main.exe} -runtime %{dep:../runtime/runtime.c} -out test014.out.gen -err test014.err.gen %{dep:test014.tig})))

(rule
 (alias runtest)
 (action (diff test014.out test014.out.gen)))

(rule
 (alias runtest)
 (action (diff test014.err test014.err.gen)))

(rule
 (targets test002.out.gen test002.err.gen)
 (action (run ../tools/run_test.exe -cmd %{dep:../src/main.exe} -runtime %{dep:../runtime/runtime.c} -out test002.out.gen -err test002.err.gen %{dep:test002.tig})))

(rule
 (alias runtest)
 (action (diff test002.out test002.out.gen)))

(rule
 (alias runtest)
 (action (diff test002.err test002.err.gen)))

(rule
 (targets test018.out.gen test018.err.gen)
 (action (run ../tools/run_test.exe -cmd %{dep:../src/main.exe} -runtime %{dep:../runtime/runtime.c} -out test018.out.gen -err test018.err.gen %{dep:test018.tig})))

(rule
 (alias runtest)
 (action (diff test018.out test018.out.gen)))

(rule
 (alias runtest)
 (action (diff test018.err test018.err.gen)))

(rule
 (targets test019.out.gen test019.err.gen)
 (action (run ../tools/run_test.exe -cmd %{dep:../src/main.exe} -runtime %{dep:../runtime/runtime.c} -out test019.out.gen -err test019.err.gen %{dep:test019.tig})))

(rule
 (alias runtest)
 (action (diff test019.out test019.out.gen)))

(rule
 (alias runtest)
 (action (diff test019.err test019.err.gen)))

(rule
 (targets test017.out.gen test017.err.gen)
 (action (run ../tools/run_test.exe -cmd %{dep:../src/main.exe} -runtime %{dep:../runtime/runtime.c} -out test017.out.gen -err test017.err.gen %{dep:test017.tig})))

(rule
 (alias runtest)
 (action (diff test017.out test017.out.gen)))

(rule
 (alias runtest)
 (action (diff test017.err test017.err.gen)))

(rule
 (targets test009.out.gen test009.err.gen)
 (action (run ../tools/run_test.exe -cmd %{dep:../src/main.exe} -runtime %{dep:../runtime/runtime.c} -out test009.out.gen -err test009.err.gen %{dep:test009.tig})))

(rule
 (alias runtest)
 (action (diff test009.out test009.out.gen)))

(rule
 (alias runtest)
 (action (diff test009.err test009.err.gen)))

(rule
 (targets test005.out.gen test005.err.gen)
 (action (run ../tools/run_test.exe -cmd %{dep:../src/main.exe} -runtime %{dep:../runtime/runtime.c} -out test005.out.gen -err test005.err.gen %{dep:test005.tig})))

(rule
 (alias runtest)
 (action (diff test005.out test005.out.gen)))

(rule
 (alias runtest)
 (action (diff test005.err test005.err.gen)))

(rule
 (targets test027.out.gen test027.err.gen)
 (action (run ../tools/run_test.exe -cmd %{dep:../src/main.exe} -runtime %{dep:../runtime/runtime.c} -out test027.out.gen -err test027.err.gen %{dep:test027.tig})))

(rule
 (alias runtest)
 (action (diff test027.out test027.out.gen)))

(rule
 (alias runtest)
 (action (diff test027.err test027.err.gen)))

(rule
 (targets test021.out.gen test021.err.gen)
 (action (run ../tools/run_test.exe -cmd %{dep:../src/main.exe} -runtime %{dep:../runtime/runtime.c} -out test021.out.gen -err test021.err.gen %{dep:test021.tig})))

(rule
 (alias runtest)
 (action (diff test021.out test021.out.gen)))

(rule
 (alias runtest)
 (action (diff test021.err test021.err.gen)))

(rule
 (targets test032.out.gen test032.err.gen)
 (action (run ../tools/run_test.exe -cmd %{dep:../src/main.exe} -runtime %{dep:../runtime/runtime.c} -out test032.out.gen -err test032.err.gen %{dep:test032.tig})))

(rule
 (alias runtest)
 (action (diff test032.out test032.out.gen)))

(rule
 (alias runtest)
 (action (diff test032.err test032.err.gen)))

(rule
 (targets test004.out.gen test004.err.gen)
 (action (run ../tools/run_test.exe -cmd %{dep:../src/main.exe} -runtime %{dep:../runtime/runtime.c} -out test004.out.gen -err test004.err.gen %{dep:test004.tig})))

(rule
 (alias runtest)
 (action (diff test004.out test004.out.gen)))

(rule
 (alias runtest)
 (action (diff test004.err test004.err.gen)))

(rule
 (targets test001.out.gen test001.err.gen)
 (action (run ../tools/run_test.exe -cmd %{dep:../src/main.exe} -runtime %{dep:../runtime/runtime.c} -out test001.out.gen -err test001.err.gen %{dep:test001.tig})))

(rule
 (alias runtest)
 (action (diff test001.out test001.out.gen)))

(rule
 (alias runtest)
 (action (diff test001.err test001.err.gen)))

(rule
 (targets test012.out.gen test012.err.gen)
 (action (run ../tools/run_test.exe -cmd %{dep:../src/main.exe} -runtime %{dep:../runtime/runtime.c} -out test012.out.gen -err test012.err.gen %{dep:test012.tig})))

(rule
 (alias runtest)
 (action (diff test012.out test012.out.gen)))

(rule
 (alias runtest)
 (action (diff test012.err test012.err.gen)))

(rule
 (targets test029.out.gen test029.err.gen)
 (action (run ../tools/run_test.exe -cmd %{dep:../src/main.exe} -runtime %{dep:../runtime/runtime.c} -out test029.out.gen -err test029.err.gen %{dep:test029.tig})))

(rule
 (alias runtest)
 (action (diff test029.out test029.out.gen)))

(rule
 (alias runtest)
 (action (diff test029.err test029.err.gen)))

(rule
 (targets test006.out.gen test006.err.gen)
 (action (run ../tools/run_test.exe -cmd %{dep:../src/main.exe} -runtime %{dep:../runtime/runtime.c} -out test006.out.gen -err test006.err.gen %{dep:test006.tig})))

(rule
 (alias runtest)
 (action (diff test006.out test006.out.gen)))

(rule
 (alias runtest)
 (action (diff test006.err test006.err.gen)))

(rule
 (targets test011.out.gen test011.err.gen)
 (action (run ../tools/run_test.exe -cmd %{dep:../src/main.exe} -runtime %{dep:../runtime/runtime.c} -out test011.out.gen -err test011.err.gen %{dep:test011.tig})))

(rule
 (alias runtest)
 (action (diff test011.out test011.out.gen)))

(rule
 (alias runtest)
 (action (diff test011.err test011.err.gen)))

(rule
 (targets test010.out.gen test010.err.gen)
 (action (run ../tools/run_test.exe -cmd %{dep:../src/main.exe} -runtime %{dep:../runtime/runtime.c} -out test010.out.gen -err test010.err.gen %{dep:test010.tig})))

(rule
 (alias runtest)
 (action (diff test010.out test010.out.gen)))

(rule
 (alias runtest)
 (action (diff test010.err test010.err.gen)))

(rule
 (targets test022.out.gen test022.err.gen)
 (action (run ../tools/run_test.exe -cmd %{dep:../src/main.exe} -runtime %{dep:../runtime/runtime.c} -out test022.out.gen -err test022.err.gen %{dep:test022.tig})))

(rule
 (alias runtest)
 (action (diff test022.out test022.out.gen)))

(rule
 (alias runtest)
 (action (diff test022.err test022.err.gen)))

(rule
 (targets test023.out.gen test023.err.gen)
 (action (run ../tools/run_test.exe -cmd %{dep:../src/main.exe} -runtime %{dep:../runtime/runtime.c} -out test023.out.gen -err test023.err.gen %{dep:test023.tig})))

(rule
 (alias runtest)
 (action (diff test023.out test023.out.gen)))

(rule
 (alias runtest)
 (action (diff test023.err test023.err.gen)))

(rule
 (targets test008.out.gen test008.err.gen)
 (action (run ../tools/run_test.exe -cmd %{dep:../src/main.exe} -runtime %{dep:../runtime/runtime.c} -out test008.out.gen -err test008.err.gen %{dep:test008.tig})))

(rule
 (alias runtest)
 (action (diff test008.out test008.out.gen)))

(rule
 (alias runtest)
 (action (diff test008.err test008.err.gen)))

(rule
 (targets test030.out.gen test030.err.gen)
 (action (run ../tools/run_test.exe -cmd %{dep:../src/main.exe} -runtime %{dep:../runtime/runtime.c} -out test030.out.gen -err test030.err.gen %{dep:test030.tig})))

(rule
 (alias runtest)
 (action (diff test030.out test030.out.gen)))

(rule
 (alias runtest)
 (action (diff test030.err test030.err.gen)))

(rule
 (targets test025.out.gen test025.err.gen)
 (action (run ../tools/run_test.exe -cmd %{dep:../src/main.exe} -runtime %{dep:../runtime/runtime.c} -out test025.out.gen -err test025.err.gen %{dep:test025.tig})))

(rule
 (alias runtest)
 (action (diff test025.out test025.out.gen)))

(rule
 (alias runtest)
 (action (diff test025.err test025.err.gen)))

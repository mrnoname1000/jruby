exclude :test_count, "expects GC.start to force GC run"
exclude :test_exception_in_finalizer_method, "broken subprocess logic"
exclude :test_exception_in_finalizer_method, "work in progress"
exclude :test_exception_in_finalizer_procs, "broken subprocess logic"
exclude :test_exception_in_finalizer_procs, "work in progress"
exclude :test_expand_heap, "broken subprocess logic"
exclude :test_gc_disabled_start, ""
exclude :test_gc_internals, "MRI-specific"
exclude :test_gc_parameter, "MRI-specific"
exclude :test_interrupt_in_finalizer, "JRuby handles signals on a separate thread, plus a lot of hinky logic in this test"
exclude :test_latest_gc_info, ""
exclude :test_latest_gc_info_argument, ""
exclude :test_start_full_mark, ""
exclude :test_start_immediate_sweep, ""
exclude :test_stat, "tests count_objects"
exclude :test_stat_constraints, ""
exclude :test_verify_internal_consistency, "no GC.verify_internal_consistency method"

exclude :"test_freeze_inside_sort!", "test bug: test expects sort to take at least 6 iterations"
exclude :test_combination_with_callcc, "Continuations are not supported"
exclude :test_flatten_with_callcc, "Continuations are not supported"
exclude :test_permutation_with_callcc, "Continuations are not supported"
exclude :test_product_with_callcc, "Continuations are not supported"
exclude :test_reject_with_callcc, "Continuations are not supported"
exclude :test_repeated_combination_with_callcc, "Continuations are not supported"
exclude :test_repeated_permutation_with_callcc, "Continuations are not supported"
exclude :test_replace_wb_variable_width_alloc, "no GC.verify_internal_consistency method"
exclude :test_shared_marking, "no GC.verify_internal_consistency method"
exclude :test_short_heap_array_sort_bang_memory_leak, "no working assert_no_memory_leak method"
exclude :test_slice_gc_compact_stress, "GC is not configurable in JRuby"
exclude :test_sort_with_callcc, "Continuations are not supported"

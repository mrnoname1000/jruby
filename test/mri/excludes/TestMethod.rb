exclude :test___dir__, "needs investigation"
exclude :test_alias_owner, "work in progress"
exclude :test_argument_error_location, "argument errors are calculated differently in JRuby"
exclude :test_bmethod_bound_parameters, "work in progress"
exclude :test_bmethod_unbound_parameters, "work in progress"
exclude :test_body, "fails due RubyVM constant"
exclude :test_bound_parameters, "work in progress"
exclude :test_callee, "fails for unoptimized define_method due to capturing a frame"
exclude :test_clone_under_gc_compact_stress, "GC is not configurable"
exclude :test_define_method_visibility, "needs investigation"
exclude :test_gced_bmethod, "often 'Timeout::Error: execution of assert_normal_exit expired' on CI"
exclude :test_hash, "won't pass since Array#map is not a Array#collect alias as in MRI"
exclude :test_kwarg_eval_memory_leak, "no working assert_no_memory_leak method"
exclude :test_method_list, "work in progress"
exclude :test_method_parameters_inspect, "work in progress"
exclude :test_prepended_public_zsuper, "2.4 fix/change to prepend + method + super_method (#4687)"
exclude :test_splat_long_array, "passes locally but fails on travis OOME"
exclude :test_super_method_alias_to_prepended_module, "work in progress"
exclude :test_to_proc_binding, "NullPointerException in parser"
exclude :test_unbound_method_parameters_inspect, "work in progress"
exclude :test_unbound_parameters, "work in progress"
exclude :test_visibility, "work in progress"
exclude :test_zsuper_method_redefined_bind_call, "visibility wrappers capture old method and don't redispatch"
exclude :test_zsuper_method_removed, "visibility wrappers capture old method and don't redispatch"
exclude :test_zsuper_method_removed_higher_method, "visibility wrappers capture old method and don't redispatch"
exclude :test_zsuper_private_override_instance_method, "visibility wrappers capture old method and don't redispatch"

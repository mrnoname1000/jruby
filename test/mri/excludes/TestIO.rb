exclude :test_autoclose_true_closed_by_finalizer, "uses RubyVM"
exclude :test_binmode_pipe, "work in progress"
exclude :test_cloexec, "needs investigation"
exclude :test_close_read_write_separately, "launches many subprocesses"
exclude :test_copy_stream_pipe_nonblock, "copy_stream does not block against a nonblocking stream (#2439)"
exclude :test_copy_stream_read_pipe, "needs investigation"
exclude :test_copy_stream_smaller, "needs investigation"
exclude :test_copy_stream_socket7, "uses fork"
exclude :test_cross_thread_close_stdio, "needs investigation"
exclude :test_dup_many, "needs investigation"
exclude :test_each_codepoint_closed, "work in progress"
exclude :test_each_line_limit_0, "needs investigation"
exclude :test_fcntl_dupfd, "needs investigation"
exclude :test_flush_in_finalizer1, "uses ObjectSpace"
exclude :test_flush_in_finalizer2, "uses ObjectSpace"
exclude :test_gets_chomp_default_rs, "needs investigation"
exclude :test_io_select_with_many_files, "creates too many files that break the rest of the suite"
exclude :test_open_redirect_keyword, "work in progress"
exclude :test_puts_recursive_ary, "needs investigation"
exclude :test_race_gets_and_close, "racey test may not be valid since gets may proceed after stream is closed"
exclude :test_read_lock, "needs investigation"
exclude :test_read_nonblock_invalid_exception, "work in progress"
exclude :test_read_nonblock_zero_size, "work in progress"
exclude :test_readlines_limit_0, "hangs"
exclude :test_readpartial_lock, "needs investigation"
exclude :test_readpartial_locktmp, "requires string locking we do not support"
exclude :test_readpartial_zero_size, "work in progress"
exclude :test_reinitialize, "needs investigation"
exclude :test_reopen_inherit, "expects inherited file descriptors and chdir through process launches; unpredictable results"
exclude :test_reopen_opt, "needs investigation"
exclude :test_s_write, "needs investigation"
exclude :test_select_exceptfds, "Java select does not really support erroring FDs"
exclude :test_select_memory_leak, "no working assert_no_memory_leak method"
exclude :test_set_lineno, "needs investigation"
exclude :test_set_stdout, "needs investigation"
exclude :test_std_fileno, "passes in isolation; some other test is causing STDIN to get a different fd"
exclude :test_stdout_to_closed_pipe, "work in progress"
exclude :test_sysread_buffer_not_raise_shared_string_error, "hangs"
exclude :test_sysread_locktmp, "requires string locking we do not support"
exclude :test_threaded_flush, "needs investigation"
exclude :test_write_nonblock_invalid_exception, "work in progress"

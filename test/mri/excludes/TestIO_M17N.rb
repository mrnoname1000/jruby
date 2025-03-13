exclude :"test_strip_bom:UTF-16LE", "work in progress"
exclude :test_both_textmode_binmode, "needs investigation"
exclude :test_cbuf, "needs investigation"
if ENV_JAVA["java.specification.version"] > "18"
  exclude :test_dup, "fails intermittently on JDK 19+ (jruby/jruby#7909)"
  exclude :test_dup_undef, "fails intermittently on JDK 19+ (jruby/jruby#7909)"
end
exclude :test_error_nonascii, "needs investigation"
exclude :test_getc_newlineconv_invalid, "needs investigation"
exclude :test_inspect_nonascii, "needs investigation"
exclude :test_open_pipe_r_enc2, "needs investigation"
exclude :test_pipe, "work in progress"
exclude :test_puts_widechar, "needs investigation"
exclude :test_set_encoding_binmode, "needs investigation"
exclude :test_set_encoding_unsupported, "needs investigation"
exclude :test_stdin_external_encoding_with_reopen, "needs investigation"
exclude :test_strip_bom, "needs investigation"
exclude :test_undef_r, "needs investigation"
exclude :test_undef_w_stateful, "needs investigation"
exclude :test_undef_w_stateless, "needs investigation"
exclude :test_ungetc_int, "needs investigation"

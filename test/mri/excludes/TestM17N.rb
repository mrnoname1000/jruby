exclude :test_index, "error message does not show BINARY (ASCII-8BIT)"
exclude :test_nonascii_method_name, "lexer is not pulling mbc characters off the wire correctly"
exclude :test_regexp_usascii, "needs investigation"
exclude :test_scrub_modification_inside_block, "missing RuntimeError"
exclude :test_sprintf_c, "invalid byte sequence in US-ASCII"
exclude :test_sprintf_p, "raising wrong error or for wrong reason"
exclude :test_str_dump, "unfinished in initial 2.6 work, #6161"
exclude :test_symbol, "management of differently-encoded symbols is not right"
exclude :test_utf_dummy_are_like_regular_dummy_encodings, "needs investigation"

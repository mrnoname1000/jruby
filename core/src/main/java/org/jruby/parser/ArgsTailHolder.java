package org.jruby.parser;

import org.jruby.ast.BlockArgNode;
import org.jruby.ast.KeywordRestArgNode;
import org.jruby.ast.ListNode;
import org.jruby.lexer.yacc.ISourcePosition;
import org.jruby.lexer.yacc.ISourcePositionHolder;

/**
 * Simple struct to hold values until they can be inserted into the AST.
 */
public class ArgsTailHolder implements ISourcePosition {
    private int line;
    private BlockArgNode blockArg;
    private ListNode keywordArgs;
    private KeywordRestArgNode keywordRestArg;
    
    public ArgsTailHolder(int line, ListNode keywordArgs,
            KeywordRestArgNode keywordRestArg, BlockArgNode blockArg) {
        this.line = line;
        this.blockArg = blockArg;
        this.keywordArgs = keywordArgs;
        this.keywordRestArg = keywordRestArg;
    }
    
    public ISourcePosition getPosition() {
        return this;
    }

    public String getFile() {
        return null;
    }

    public int getLine() {
        return line;
    }
    
    public BlockArgNode getBlockArg() {
        return blockArg;
    }
    
    public ListNode getKeywordArgs() {
        return keywordArgs;
    }
    
    public KeywordRestArgNode getKeywordRestArgNode() {
        return keywordRestArg;
    }
    
    /**
     * Does this holder support either keyword argument types
     */
    public boolean hasKeywordArgs() {
        return keywordArgs != null || keywordRestArg != null;
    }
}

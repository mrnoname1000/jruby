/*
 ***** BEGIN LICENSE BLOCK *****
 * Version: EPL 2.0/GPL 2.0/LGPL 2.1
 *
 * The contents of this file are subject to the Eclipse Public
 * License Version 2.0 (the "License"); you may not use this file
 * except in compliance with the License. You may obtain a copy of
 * the License at http://www.eclipse.org/legal/epl-v20.html
 *
 * Software distributed under the License is distributed on an "AS
 * IS" basis, WITHOUT WARRANTY OF ANY KIND, either express or
 * implied. See the License for the specific language governing
 * rights and limitations under the License.
 *
 * Copyright (C) 2001-2002 Jan Arne Petersen <jpetersen@uni-bonn.de>
 * Copyright (C) 2001-2002 Benoit Cerrina <b.cerrina@wanadoo.fr>
 * Copyright (C) 2002-2004 Anders Bengtsson <ndrsbngtssn@yahoo.se>
 * Copyright (C) 2004 Thomas E Enebo <enebo@acm.org>
 * Copyright (C) 2004 Stefan Matthias Aust <sma@3plus4.de>
 * Copyright (C) 2006 Thomas Corbat <tcorbat@hsr.ch>
 * 
 * Alternatively, the contents of this file may be used under the terms of
 * either of the GNU General Public License Version 2 or later (the "GPL"),
 * or the GNU Lesser General Public License Version 2.1 or later (the "LGPL"),
 * in which case the provisions of the GPL or the LGPL are applicable instead
 * of those above. If you wish to allow use of your version of this file only
 * under the terms of either the GPL or the LGPL, and not to allow others to
 * use your version of this file under the terms of the EPL, indicate your
 * decision by deleting the provisions above and replace them with the notice
 * and other provisions required by the GPL or the LGPL. If you do not delete
 * the provisions above, a recipient may use your version of this file under
 * the terms of any one of the EPL, the GPL or the LGPL.
 ***** END LICENSE BLOCK *****/

package org.jruby.ast;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import org.jruby.ast.types.INameNode;
import org.jruby.ast.visitor.NodeVisitor;

/**
 * Base class for all Nodes in the AST
 */
public abstract class Node {
    // We define an actual list to get around bug in java integration (1387115)
    static final List<Node> EMPTY_LIST = new ArrayList<>();

    private int line;
    
    // Does this node contain a node which is an assignment.  We can use this knowledge when emitting IR
    // instructions to do more or less depending on whether we have to cope with scenarios like:
    //    a = 1; [a, a = 2];
    // in IR, we can see that ArrayNode contains an assignment and emit its individual elements differently
    // so that the two values of a end up being different.
    protected boolean containsVariableAssignment;
    protected boolean newline;

    public Node(int line, boolean containsAssignment) {
        this.line = line;
        this.containsVariableAssignment = containsAssignment;
    }

    public void setNewline() {
        this.newline = true;
    }

    // Used by heredoc dedent processing.  It gets unset so we do not liter line events because of it.
    public void unsetNewline() {
        this.newline = false;
    }

    public boolean isNewline() {
        return newline;
    }

    public int getLine() {
        return line;
    }

    public String getFile() {
        return null;
    }

    public void setLine(int line) {
        this.line = line;
    }
    
    public abstract <T> T accept(NodeVisitor<T> visitor);
    public abstract List<Node> childNodes();

    protected static List<Node> createList(Node node) {
        return Collections.singletonList(node);
    }

    protected static List<Node> createList(Node node1, Node node2) {
        ArrayList<Node> list = new ArrayList<>(2);

        list.add(node1);
        list.add(node2);

        return list;
    }

    protected static List<Node> createList(Node node1, Node node2, Node node3) {
        ArrayList<Node> list = new ArrayList<>(3);

        list.add(node1);
        list.add(node2);
        list.add(node3);

        return list;
    }

    protected static List<Node> createList(Node... nodes) {
        ArrayList<Node> list = new ArrayList<>(nodes.length);
        
        for (Node node: nodes) {
            if (node != null) list.add(node);
        }
        
        return list;
    }

    @Override
    public String toString() {
        return toString(false, 0);
    }

    /**
     * Not all interesting info in the AST is from Node data.  This method will print
     * out anything else of note (e.g. FixnumNode's long value).
     * @return null for no extra info or something otherwise.
     */
    public String toStringExtraInfo() {
       return null;
    }

    public String toString(boolean indent, int indentation) {
        if (this instanceof InvisibleNode) return "";

        StringBuilder builder = new StringBuilder(60);

        if (indent) indent(indentation, builder);

        builder.append('(').append(getNodeName());

        if (isNewline()) builder.append('*');

        String moreState = toStringInternal();

        if (moreState != null) builder.append("[").append(moreState).append("]");

        if (this instanceof INameNode) builder.append(":").append(((INameNode) this).getName());

        builder.append(" line: ").append(getLine());

        String extraInfo = toStringExtraInfo();
        if (extraInfo != null) builder.append(", ").append(extraInfo);

        if (!childNodes().isEmpty() && indent) builder.append("\n");

        for (Node child : childNodes()) {
            if (!indent) builder.append(", ");

            if (child == null) {
                if (indent) indent(indentation + 1, builder);

                builder.append("null");
            } else {
                if (indent && child instanceof NilImplicitNode) {
                    indent(indentation + 1, builder);

                    builder.append(child.getClass().getSimpleName());
                } else {
                    builder.append(child.toString(indent, indentation + 1));
                }
            }

            if (indent) builder.append("\n");
        }

        if (!childNodes().isEmpty() && indent) indent(indentation, builder);

        builder.append(")");

        return builder.toString();
    }

    /**
     * Overridden by nodes that have additional internal state to be displated in toString.
     * <p>
     * For nodes that have it, name is handled separately, by implementing INameNode.
     * <p>
     * Child nodes are handled via iterating #childNodes.
     *
     * @return A string representing internal node state, or null if none.
     */
    protected String toStringInternal() {
        return null;
    }

    private static void indent(int indentation, StringBuilder builder) {
        builder.append("  ".repeat(Math.max(0, indentation)));
    }

    protected String getNodeName() {
        String name = getClass().getName();
        return name.substring(name.lastIndexOf('.') + 1);
    }

    /**
     * @return the nodeId
     */
    public abstract NodeType getNodeType();

    /**
     * Whether the node evaluates to nil and has no side effects.
     *
     * @return true if nil, false otherwise
     */
    public boolean isNil() {
        return false;
    }

    /**
     * Check whether the given node is considered always "defined" or whether it
     * has some form of definition check.
     *
     * @return Whether the type of node represents a possibly undefined construct
     */
    public boolean needsDefinitionCheck() {
        return true;
    }

    /**
     * Does this node or one of its children contain an assignment?
     */
    public boolean containsVariableAssignment() {
        return containsVariableAssignment;
    }

    /**
     * @return is it possible this node will execute only once.  Note: This is not
     * comprehensive.  It is used to look from root node down to class/module nodes
     * to make sure that narrow case can execute once.  It is possible much deeper
     * down the tree some nodes can only execute once but it will be marked as false
     * because that case is not what this is for.
     */
    public boolean executesOnce() {
        return false;
    }
}

package org.jruby.ir.instructions;

import org.jruby.RubyInstanceConfig;
import org.jruby.RubySymbol;
import org.jruby.ir.IRScope;
import org.jruby.ir.IRVisitor;
import org.jruby.ir.Operation;
import org.jruby.ir.instructions.specialized.OneArgOperandAttrAssignInstr;
import org.jruby.ir.operands.Operand;
import org.jruby.ir.operands.Self;
import org.jruby.ir.persistence.IRReaderDecoder;
import org.jruby.ir.persistence.IRWriterEncoder;
import org.jruby.ir.transformations.inlining.CloneInfo;
import org.jruby.parser.StaticScope;
import org.jruby.runtime.*;
import org.jruby.runtime.builtin.IRubyObject;

// Instruction representing Ruby code of the form: "a[i] = 5"
// which is equivalent to: a.[]=(i,5)
public class AttrAssignInstr extends NoResultCallInstr {
    public static AttrAssignInstr create(IRScope scope, Operand obj, RubySymbol attr, Operand[] args, boolean isPotentiallyRefined) {
        if (!containsArgSplat(args) && args.length == 1) {
            return new OneArgOperandAttrAssignInstr(scope, obj, attr, args, isPotentiallyRefined);
        }

        return new AttrAssignInstr(scope, obj, attr, args, isPotentiallyRefined);
    }

    public AttrAssignInstr(IRScope scope, Operand obj, RubySymbol attr, Operand[] args, boolean isPotentiallyRefined) {
        super(scope, Operation.ATTR_ASSIGN, obj instanceof Self ? CallType.FUNCTIONAL : CallType.NORMAL, attr, obj, args, null, isPotentiallyRefined);
    }

    @Override
    public Instr clone(CloneInfo ii) {
        return new AttrAssignInstr(ii.getScope(), getReceiver().cloneForInlining(ii), getName(), cloneCallArgs(ii), isPotentiallyRefined());
    }

    @Override
    public void encode(IRWriterEncoder e) {
        if (RubyInstanceConfig.IR_WRITING_DEBUG) System.out.println("Instr(" + getOperation() + "): " + this);
        e.encode(getOperation());
        e.encode(getReceiver());
        e.encode(getName());
        e.encode(getCallArgs());
    }

    public static AttrAssignInstr decode(IRReaderDecoder d) {
        return create(d.getCurrentScope(), d.decodeOperand(), d.decodeSymbol(), d.decodeOperandArray(), d.getCurrentScope().maybeUsingRefinements());
    }

    @Override
    public Object interpret(ThreadContext context, StaticScope currScope, DynamicScope dynamicScope, IRubyObject self, Object[] temp) {
        IRubyObject object = (IRubyObject) getReceiver().retrieve(context, self, currScope, dynamicScope, temp);
        IRubyObject[] values = prepareArguments(context, self, currScope, dynamicScope, temp);

        callSite.call(context, self, object, values);

        return null;
    }

    @Override
    public void visit(IRVisitor visitor) {
        visitor.AttrAssignInstr(this);
    }
}

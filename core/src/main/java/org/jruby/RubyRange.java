/***** BEGIN LICENSE BLOCK *****
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
 * Copyright (C) 2001 Chad Fowler <chadfowler@chadfowler.com>
 * Copyright (C) 2001 Alan Moore <alan_moore@gmx.net>
 * Copyright (C) 2001 Ed Sinjiashvili <slorcim@users.sourceforge.net>
 * Copyright (C) 2001-2004 Jan Arne Petersen <jpetersen@uni-bonn.de>
 * Copyright (C) 2002 Benoit Cerrina <b.cerrina@wanadoo.fr>
 * Copyright (C) 2002-2006 Thomas E Enebo <enebo@acm.org>
 * Copyright (C) 2002-2004 Anders Bengtsson <ndrsbngtssn@yahoo.se>
 * Copyright (C) 2004 Stefan Matthias Aust <sma@3plus4.de>
 * Copyright (C) 2005 Charles O Nutter <headius@headius.com>
 * Copyright (C) 2006 Miguel Covarrubias <mlcovarrubias@gmail.com>
 *
 * Alternatively, the contents of this file may be used under the terms of
 * either of the GNU General Public License Version 2 or later (the "GPL"), or
 * the GNU Lesser General Public License Version 2.1 or later (the "LGPL"), in
 * which case the provisions of the GPL or the LGPL are applicable instead of
 * those above. If you wish to allow use of your version of this file only under
 * the terms of either the GPL or the LGPL, and not to allow others to use your
 * version of this file under the terms of the EPL, indicate your decision by
 * deleting the provisions above and replace them with the notice and other
 * provisions required by the GPL or the LGPL. If you do not delete the
 * provisions above, a recipient may use your version of this file under the
 * terms of any one of the EPL, the GPL or the LGPL.
 ***** END LICENSE BLOCK *****/

package org.jruby;


import java.io.IOException;
import java.util.List;

import org.jruby.anno.JRubyClass;
import org.jruby.anno.JRubyMethod;
import org.jruby.api.API;
import org.jruby.api.JRubyAPI;
import org.jruby.exceptions.JumpException;
import org.jruby.runtime.Arity;
import org.jruby.runtime.Block;
import org.jruby.runtime.BlockCallback;
import org.jruby.runtime.CallBlock;
import org.jruby.runtime.CallSite;
import org.jruby.runtime.ClassIndex;
import org.jruby.runtime.Helpers;
import org.jruby.runtime.JavaSites;
import org.jruby.runtime.ObjectMarshal;
import org.jruby.runtime.Signature;
import org.jruby.runtime.ThreadContext;

import static org.jruby.RubyEnumerator.enumeratorizeWithSize;
import static org.jruby.RubyNumeric.*;
import static org.jruby.api.Convert.*;
import static org.jruby.api.Create.*;
import static org.jruby.api.Define.defineClass;
import static org.jruby.api.Error.*;
import static org.jruby.runtime.Helpers.hashEnd;
import static org.jruby.runtime.Helpers.hashStart;
import static org.jruby.runtime.Helpers.invokedynamic;
import static org.jruby.runtime.Helpers.murmurCombine;
import static org.jruby.runtime.Helpers.safeHash;

import org.jruby.runtime.builtin.IRubyObject;
import org.jruby.runtime.builtin.Variable;
import org.jruby.runtime.callsite.RespondToCallSite;
import org.jruby.runtime.component.VariableEntry;
import org.jruby.runtime.invokedynamic.MethodNames;
import org.jruby.runtime.marshal.MarshalStream;
import org.jruby.runtime.marshal.NewMarshal;
import org.jruby.runtime.marshal.UnmarshalStream;
import org.jruby.util.Numeric;
import org.jruby.util.TypeConverter;

import static org.jruby.RubyEnumerator.SizeFn;

import static org.jruby.runtime.Visibility.PRIVATE;
import static org.jruby.util.RubyStringBuilder.str;
import static org.jruby.util.RubyStringBuilder.types;

/**
 * @author jpetersen
 */
@JRubyClass(name = "Range", include = "Enumerable")
public class RubyRange extends RubyObject {

    private IRubyObject begin;
    private IRubyObject end;
    private boolean isBeginless;
    private boolean isExclusive;
    private boolean isEndless;
    private boolean isInited = false;

    public static RubyClass createRangeClass(ThreadContext context, RubyClass Object, RubyModule Enumerable) {
        RubyClass Range = defineClass(context, "Range", Object, RubyRange::new).
                reifiedClass(RubyRange.class).
                marshalWith(RANGE_MARSHAL).
                kindOf(new RubyModule.JavaClassKindOf(RubyRange.class)).
                classIndex(ClassIndex.RANGE).
                include(context, Enumerable).
                defineMethods(context, RubyRange.class);

        Range.defineClassUnder(context, "BSearch", Object, OBJECT_ALLOCATOR).defineMethods(context, BSearch.class);

        Range.setConstantVisibility(context.runtime, "BSearch", true);

        return Range;
    }

    private RubyRange(Ruby runtime, RubyClass klass) {
        super(runtime, klass);
        begin = end = runtime.getNil();
    }

    public static RubyRange newRange(ThreadContext context, IRubyObject begin, IRubyObject end, boolean isExclusive) {
        RubyRange range = new RubyRange(context.runtime, context.runtime.getRange());
        range.init(context, begin, end, isExclusive);
        range.isInited = true;
        return range;
    }

    public static RubyRange newBeginlessRange(ThreadContext context, long end, boolean isExclusive) {
        Ruby runtime = context.runtime;
        RubyRange range = new RubyRange(runtime, runtime.getRange());
        range.init(context, context.nil, asFixnum(context, end), isExclusive);
        range.isInited = true;
        return range;
    }

    public static RubyRange newEndlessRange(ThreadContext context, long begin, boolean isExclusive) {
        Ruby runtime = context.runtime;
        RubyRange range = new RubyRange(runtime, runtime.getRange());
        range.init(context, asFixnum(context, begin), context.nil, isExclusive);
        range.isInited = true;
        return range;
    }

    public static RubyRange newRange(ThreadContext context, long begin, long end, boolean isExclusive) {
        Ruby runtime = context.runtime;
        RubyRange range = new RubyRange(runtime, runtime.getRange());
        range.init(context, asFixnum(context, begin), asFixnum(context, end), isExclusive);
        range.isInited = true;
        return range;
    }

    public static RubyRange newInclusiveRange(ThreadContext context, IRubyObject begin, IRubyObject end) {
        return newRange(context, begin, end, false);
    }

    public static RubyRange newInclusiveRange(ThreadContext context, long begin, long end) {
        return newRange(context, begin, end, false);
    }

    public static RubyRange newExclusiveRange(ThreadContext context, IRubyObject begin, IRubyObject end) {
        return newRange(context, begin, end, true);
    }

    public static RubyRange newExclusiveRange(ThreadContext context, long begin, long end) {
        return newRange(context, begin, end, true);
    }

    @Override
    public void copySpecialInstanceVariables(IRubyObject clone) {
        RubyRange range = (RubyRange) clone;
        range.begin = begin;
        range.end = end;
        range.isExclusive = isExclusive;
    }

    final boolean checkBegin(ThreadContext context, long length) {
        long beg = isBeginless ? 0 : numericToLong(context, this.begin);
        if (beg < 0) {
            beg += length;
            if (beg < 0) {
                return false;
            }
        } else if (length < beg) {
            return false;
        }
        return true;
    }

    final long[] begLen(ThreadContext context, long len, int err) {
        long beg = isBeginless ? 0 : numericToLong(context, this.begin);
        long end = isEndless ? -1: numericToLong(context, this.end);

        if (beg < 0) {
            beg += len;
            if (beg < 0) {
                if (err != 0) throw rangeError(context, beg + ".." + (isExclusive ? "." : "") + end + " out of range");
                return null;
            }
        }

        if (err == 0 || err == 2) {
            if (beg > len) {
                if (err != 0) throw rangeError(context, beg + ".." + (isExclusive ? "." : "") + end + " out of range");
                return null;
            }
            if (end > len) end = len;
        }

        if (end < 0) end += len;
        if (!isExclusive || isEndless) end++;

        len = end - beg;
        if (len < 0) len = 0;

        return new long[]{beg, len};
    }

    final long begLen0(ThreadContext context, long len) {
        long beg = isBeginless ? 0 : numericToLong(context, this.begin);

        if (beg < 0) {
            beg += len;
            if (beg < 0) throw rangeError(context, (beg - len) + ".." + (isExclusive ? "." : "") + end + " out of range");
        }

        return beg;
    }

    final long begLen1(ThreadContext context, long len, long beg) {
        long end = isEndless ? -1 : numericToLong(context, this.end);

        if (end < 0) end += len;
        if (!isExclusive || isEndless) end++;

        len = end - beg;
        if (len < 0) len = 0;

        return len;
    }

    @Deprecated(since = "10.0", forRemoval = true)
    final int[] begLenInt(int len, final int err) {
        return begLenInt(getCurrentContext(), len, err);
    }

    // MRI: rb_range_component_beg_len
    final int[] begLenInt(ThreadContext context, int len, final int err) {
        int beg = isBeginless ? 0 : RubyNumeric.num2int(this.begin);
        int end = isEndless ? -1 : RubyNumeric.num2int(this.end);

        if (beg < 0) {
            beg += len;
            if (beg < 0) {
                if (err != 0) throw rangeError(context, begin + ".." + (isExclusive ? "." : "") + this.end + " out of range");
                return null;
            }
        }

        if (err == 0 || err == 2) {
            if (beg > len) {
                if (err != 0) throw rangeError(context, begin + ".." + (isExclusive ? "." : "") + this.end + " out of range");
                return null;
            }
            if (end > len) {
                end = len;
            }
        }

        if (end < 0) end += len;
        if (!isExclusive || isEndless) end++;

        len = end - beg;
        if (len < 0) len = 0;

        return new int[]{beg, len};
    }

    private void init(ThreadContext context, IRubyObject begin, IRubyObject end, boolean isExclusive) {
        if (!(begin instanceof RubyFixnum && end instanceof RubyFixnum) && !end.isNil() && !begin.isNil()) {
            IRubyObject result = invokedynamic(context, begin, MethodNames.OP_CMP, end);
            if (result.isNil()) throw argumentError(context, "bad value for range");
        }

        this.begin = begin;
        this.end = end;
        this.isExclusive = isExclusive;
        this.isEndless = end.isNil();
        this.isBeginless = begin.isNil();
        this.isInited = true;
        if (metaClass.getClassIndex() == ClassIndex.RANGE) this.setFrozen(true);
    }

    @JRubyMethod(required = 2, optional = 1, checkArity = false, visibility = PRIVATE)
    public IRubyObject initialize(ThreadContext context, IRubyObject[] args, Block unusedBlock) {
        Arity.checkArgumentCount(context, args, 2, 3);

        if (this.isInited) throw context.runtime.newFrozenError("`initialize' called twice", this);
        checkFrozen();
        init(context, args[0], args[1], args.length > 2 && args[2].isTrue());
        this.isInited = true;
        return context.nil;
    }

    @JRubyMethod(visibility = PRIVATE)
    public IRubyObject initialize_copy(ThreadContext context, IRubyObject original) {
        if (this.isInited) throw context.runtime.newFrozenError("`initialize' called twice", this);

        RubyRange other = (RubyRange) original;
        this.begin = other.begin;
        this.end = other.end;
        this.isExclusive = other.isExclusive;
        this.isEndless = other.end.isNil();
        this.isBeginless = other.begin.isNil();
        this.isInited = true;
        return context.nil;
    }

    @Override
    public RubyFixnum hash() {
        return hash(metaClass.runtime.getCurrentContext());
    }

    @JRubyMethod(name = "hash")
    public RubyFixnum hash(ThreadContext context) {
        int exclusiveBit = isExclusive ? 1 : 0;
        long hash = exclusiveBit;

        hash = hashStart(context.runtime, hash);
        IRubyObject v = safeHash(context, begin);
        hash = murmurCombine(hash, v.convertToInteger().getLongValue());
        v = safeHash(context, end);
        hash = murmurCombine(hash, v.convertToInteger().getLongValue());
        hash = murmurCombine(hash, exclusiveBit << 24);
        hash = hashEnd(hash);

        return asFixnum(context, hash);
    }

    private static RubyString inspectValue(final ThreadContext context, IRubyObject value) {
        return (RubyString) context.safeRecurse(RubyRange::inspectValueRecursive, value, value, "inspect", true);
    }

    private static IRubyObject inspectValueRecursive(ThreadContext context, IRubyObject state, IRubyObject obj, boolean recur) {
        return recur ?
                newString(context, ((RubyRange) obj).isExclusive ? "(... ... ...)" : "(... .. ...)") :
                inspect(context, obj);
    }

    private static final byte[] DOTDOTDOT = new byte[]{'.', '.', '.'};

    @Override
    public IRubyObject inspect() {
        return inspect(getRuntime().getCurrentContext());
    }

    @JRubyMethod(name = "inspect")
    public RubyString inspect(final ThreadContext context) {
        RubyString i1 = isBeginless && !isEndless ? newEmptyString(context) : dupString(context, inspectValue(context, begin));
        RubyString i2 = isEndless && !isBeginless ? newEmptyString(context) : inspectValue(context, end);
        i1.cat(DOTDOTDOT, 0, isExclusive ? 3 : 2);
        i1.append(i2);
        return i1;
    }

    @Override
    @JRubyMethod(name = "to_s")
    public IRubyObject to_s(final ThreadContext context) {
        return to_s(context.runtime);
    }

    private RubyString to_s(final Ruby runtime) {
        RubyString i1 = begin.asString().strDup(runtime);
        RubyString i2 = end.asString();
        i1.cat(DOTDOTDOT, 0, isExclusive ? 3 : 2);
        i1.append(i2);
        return i1;
    }

    @JRubyMethod(name = "exclude_end?")
    public RubyBoolean exclude_end_p(ThreadContext context) {
        return asBoolean(context, isExclusive);
    }

    @Deprecated
    public RubyBoolean exclude_end_p() {
        return exclude_end_p(getRuntime().getCurrentContext());
    }
    
    @JRubyMethod(name = "eql?")
    public IRubyObject eql_p(ThreadContext context, IRubyObject other) {
        return equalityInner(context, other, MethodNames.EQL);
    }

    @JRubyMethod(name = "==")
    public IRubyObject op_equal(ThreadContext context, IRubyObject other) {
        return equalityInner(context, other, MethodNames.OP_EQUAL);
    }

    private IRubyObject equalityInner(ThreadContext context, IRubyObject other, MethodNames equalityCheck) {
        if (this == other) return context.tru;
        if (!(other instanceof RubyRange)) return context.fals;

        RubyRange otherRange = (RubyRange) other;

        return asBoolean(context, isExclusive == otherRange.isExclusive &&
                invokedynamic(context, this.begin, equalityCheck, otherRange.begin).isTrue() &&
                invokedynamic(context, this.end, equalityCheck, otherRange.end).isTrue());
    }

    private interface RangeCallBack {
        void doCall(ThreadContext context, IRubyObject arg);
    }

    private static class StepBlockCallBack implements RangeCallBack, BlockCallback {

        final Block block;
        IRubyObject iter;
        final IRubyObject step;

        StepBlockCallBack(Block block, RubyFixnum iter, IRubyObject step) {
            this.block = block;
            this.iter = iter;
            this.step = step;
        }

        public IRubyObject call(ThreadContext context, IRubyObject[] args, Block originalBlock) {
            doCall(context, args[0]);
            return context.nil;
        }

        @Override
        public void doCall(ThreadContext context, IRubyObject arg) {
            if (iter instanceof RubyFixnum iterFixnum) {
                iter = asFixnum(context, iterFixnum.getLongValue() - 1);
            } else if (iter instanceof RubyInteger iterInteger) {
                iter = iterInteger.op_minus(context, 1);
            } else {
                iter = iter.callMethod(context, "-", one(context));
            }
            IRubyObject i = this.iter;
            if ((i instanceof RubyInteger) && ((RubyInteger) i).isZero()) {
                doYield(context, arg);
                iter = step;
            }
        }

        protected void doYield(ThreadContext context, IRubyObject arg) {
            block.yield(context, arg);
        }

        transient RubyFixnum one;

        private RubyFixnum one(ThreadContext context) {
            RubyFixnum one = this.one;
            if (one == null) {
                one = this.one = RubyFixnum.one(context.runtime);
            }
            return one;
        }

    }

    private static class SymbolStepBlockCallBack extends StepBlockCallBack {
        SymbolStepBlockCallBack(Block block, RubyFixnum iter, IRubyObject step) {
            super(block, iter, step);
        }

        protected void doYield(ThreadContext context, IRubyObject arg) {
            block.yield(context, ((RubyString) arg).intern());
        }
    }

    private static boolean isZero(IRubyObject num) {
        return num instanceof RubyFixnum && ((RubyNumeric) num).isZero();
    }

    private static IRubyObject rangeLt(ThreadContext context, IRubyObject a, IRubyObject b) {
        return rangeLess(context, a, b) < 0 ? context.tru : null;
    }

    // MRI: r_less
    private static int rangeLess(ThreadContext context, IRubyObject a, IRubyObject b) {
        IRubyObject result = invokedynamic(context, a, MethodNames.OP_CMP, b);

        if (result.isNil()) {
            return Integer.MAX_VALUE;
        }

        return RubyComparable.cmpint(context, result, a, b);
    }

    private static IRubyObject rangeLe(ThreadContext context, IRubyObject a, IRubyObject b) {
        IRubyObject result = invokedynamic(context, a, MethodNames.OP_CMP, b);
        if (result.isNil()) {
            return null;
        }
        int c = RubyComparable.cmpint(context, result, a, b);
        if (c == 0) {
            return RubyFixnum.zero(context.runtime);
        }
        return c < 0 ? context.tru : null;
    }

    private void rangeEach(ThreadContext context, RangeCallBack callback) {
        IRubyObject v = begin;
        if (isExclusive) {
            while (rangeLt(context, v, end) != null) {
                callback.doCall(context, v);
                v = v.callMethod(context, "succ");
                context.pollThreadEvents();
            }
        } else {
            IRubyObject c;
            while ((c = rangeLe(context, v, end)) != null && c.isTrue()) {
                callback.doCall(context, v);
                if (isZero(c)) {
                    break;
                }
                v = v.callMethod(context, "succ");
                context.pollThreadEvents();
            }
        }
    }

    private boolean coverRangeP(ThreadContext context, IRubyObject val) {
        if (begin.isNil() || rangeLess(context, begin, val) <= 0) {
            int excl = isExclusive ? 1 : 0;
            return end.isNil() || rangeLess(context, end, val) <= -excl;
        }

        return false;
    }

    private boolean coverRange(ThreadContext context, RubyRange val) {
        int cmp;

        IRubyObject valBeg = val.begin;
        IRubyObject valEnd = val.end;

        int excl = isExclusive ? 1 : 0;
        int valExcl = val.isExclusive ? 1 : 0;

        if (!end.isNil() && valEnd.isNil()) return false;
        if (!begin.isNil() && valBeg.isNil()) return false;
        if (!valBeg.isNil() && !valEnd.isNil() && rangeLess(context, valBeg, valEnd) > -valExcl) return false;
        if (!valBeg.isNil() && !cover_p(context, valBeg).isTrue()) return false;

        cmp = rangeLess(context, end, valEnd);
        if (excl == valExcl) {
            return cmp >= 0;
        } else if (excl != 0) {
            return cmp > 0;
        } else if (cmp >= 0) {
            return true;
        }

        IRubyObject nil = context.nil;

        IRubyObject valMax = API.rescueTypeError(context, nil, () -> sites(context).max.call(context, this, val));

        if (valMax == nil) return false;

        cmp = rangeLess(context, end, valMax);
        return cmp >= 0 && cmp != Integer.MAX_VALUE;
    }

    @JRubyMethod
    public IRubyObject to_a(ThreadContext context, final Block block) {
        if (isEndless) throw rangeError(context, "cannot convert endless range to an array");
        return RubyEnumerable.to_a(context, this);
    }

    @JRubyMethod(name = "each")
    public IRubyObject each(final ThreadContext context, final Block block) {
        if (!block.isGiven()) {
            return enumeratorizeWithSize(context, this, "each", RubyRange::size);
        }
        if (begin instanceof RubyFixnum begFixnum && isEndless) {
            begFixnum.step(context, IRubyObject.NULL_ARRAY, block);
        } else if (begin instanceof RubyFixnum && end instanceof RubyFixnum) {
            fixnumEach(context, block);
        } else if (begin instanceof RubySymbol && end instanceof RubySymbol) {
            begin.asString().uptoCommon(context, end.asString(), isExclusive, block, true);
        } else {
            IRubyObject tmp = begin.checkStringType();
            if (!tmp.isNil()) {
                if (isEndless) {
                    ((RubyString) tmp).uptoEndless(context, block);
                } else {
                    ((RubyString) tmp).uptoCommon(context, end, isExclusive, block);
                }
            } else {
                if (!discreteObject(context, begin)) throw typeError(context, "can't iterate from ", begin, "");
                if (!end.isNil()) {
                    rangeEach(context, (ThreadContext ctx, IRubyObject arg) -> block.yield(ctx, arg));
                } else {
                    for (IRubyObject beg = begin;; beg = beg.callMethod(context, "succ")) {
                        block.yield(context, beg);
                        context.pollThreadEvents();
                    }
                }
            }
        }
        return this;
    }

    private void fixnumEach(ThreadContext context, Block block) {
        // We must avoid integer overflows.
        long to = ((RubyFixnum) end).value;
        if (isExclusive) {
            if (to == Long.MIN_VALUE) {
                return;
            }
            to--;
        }
        RubyInteger.fixnumUpto(context, ((RubyFixnum) begin).value, to, block);
    }

    // MRI: range_reverse_each
    @JRubyMethod
    public IRubyObject reverse_each(ThreadContext context, Block block) {
        if (!block.isGiven()) {
            return enumeratorizeWithSize(context, this, "reverse_each", RubyRange::size);
        }

        IRubyObject beg = this.begin;
        IRubyObject end = this.end;
        boolean excl = isExclusive;

        if (end.isNil()) throw typeError(context, "can't iterate from ", end, "");

        if (beg instanceof RubyFixnum && end instanceof RubyFixnum endFixnum) {
            if (excl) {
                if (endFixnum.getLongValue() == RubyFixnum.MIN) return this;

                end = endFixnum.op_minus(context, 1);
            }

            reverseEachFixnum(context, beg, (RubyInteger) end, block);
        } else if ((beg.isNil() || beg instanceof RubyInteger) && end instanceof RubyInteger endInteger) {
            if (excl) {
                endInteger = (RubyInteger) endInteger.op_minus(context, 1);
            }

            reverseEachPositiveBignum(context, beg, endInteger, block);
            reverseEachFixnum(context, beg, endInteger, block);
            reverseEachNegativeBignum(context, beg, endInteger, block);
        } else {
            return RubyEnumerable.reverse_each(context, this, block);
        }

        return this;
    }

    // MRI: range_reverse_each_fixnum_section
    private void reverseEachFixnum(ThreadContext context, IRubyObject beg, RubyInteger end, Block block) {
        if (beg.isNil()) {
            beg = asFixnum(context, RubyFixnum.MIN);
        }

        reverseEachFixnum(context, (RubyInteger) beg, end, block);
    }

    // MRI: range_reverse_each_fixnum_section
    private void reverseEachFixnum(ThreadContext context, RubyInteger beg, RubyInteger end, Block block) {
        assert (!end.isNil());

        if (!(beg instanceof RubyFixnum)) {
            if (!beg.isNil() && bignumPositive(beg)) return;

            beg = asFixnum(context, RubyFixnum.MIN);
        }

        if (!(end instanceof RubyFixnum)) {
            if (bignumNegative(end)) return;

            end = asFixnum(context, RubyFixnum.MAX);
        }

        long b = fix2long(beg);
        long e = fix2long(end);

        for (long i = e; i >= b; --i) {
            block.yieldSpecific(context, asFixnum(context, i));
            // avoid underflow
            if (i == b) break;
        }
    }

    // MRI: range_reverse_each_positive_bignum_section
    private void reverseEachPositiveBignum(ThreadContext context, IRubyObject beg, RubyInteger end, Block block) {
        assert (!end.isNil());

        if (end instanceof RubyFixnum || bignumNegative(end)) return;

        if (beg.isNil() || beg instanceof RubyFixnum || bignumNegative(beg)) {
            beg = RubyBignum.newBignum(context.runtime, RubyBignum.LONG_MAX_PLUS_ONE);
        }

        reverseEachBignum(context, (RubyInteger) beg, end, block);
    }

    // MRI: range_reverse_each_negative_bignum_section
    private void reverseEachNegativeBignum(ThreadContext context, IRubyObject beg, RubyInteger end, Block block) {
        assert (!end.isNil());

        if (end instanceof RubyFixnum || bignumPositive(end)) {
            end = RubyBignum.newBignum(context.runtime, RubyBignum.LONG_MIN_MINUS_ONE);
        }

        if (beg.isNil()) {
            reverseEachBignumBeginless(context, end, block);
        }

        if (beg instanceof RubyFixnum || bignumPositive(beg)) return;

        reverseEachBignum(context, (RubyInteger) beg, end, block);
    }

    // MRI: range_reverse_each_bignum
    private void reverseEachBignum(ThreadContext context, RubyInteger beg, RubyInteger end, Block block) {
        assert (bignumPositive(beg) == bignumPositive(end));

        Ruby runtime = context.runtime;
        RubyFixnum one = RubyFixnum.one(runtime);
        RubyFixnum zero = RubyFixnum.zero(runtime);

        IRubyObject c;
        while (!(c = beg.op_cmp(context, end)).equals(one)) {
            block.yieldSpecific(context, end);
            if (c == zero) break;
            end = (RubyInteger) end.op_minus(context, one);
        }
    }

    // MRI: range_reverse_each_bignum_beginless
    private void reverseEachBignumBeginless(ThreadContext context, RubyInteger end, Block block) {
        assert (bignumNegative(end));

        for (; ; end = (RubyInteger) end.op_minus(context, 1)) {
            block.yieldSpecific(context, end);
        }
    }

    // MRI: RBIGNUM_NEGATIVE
    private static boolean bignumNegative(IRubyObject end) {
        assert (end instanceof RubyBignum);
        RubyBignum bigEnd = (RubyBignum) end;
        return bigEnd.signum() == -1;
    }

    // MRI: RBIGNUM_POSITIVE
    private static boolean bignumPositive(IRubyObject num) {
        assert (num instanceof RubyBignum);
        RubyBignum bigNum = (RubyBignum) num;
        return bigNum.signum() == 1;
    }

    @JRubyMethod(name = "step")
    public IRubyObject step(final ThreadContext context, final Block block) {
        return block.isGiven() ? stepCommon(context, RubyFixnum.one(context.runtime), block) : step(context, context.runtime.getNil(), block);
    }

    @JRubyMethod(name = "step")
    public IRubyObject step(final ThreadContext context, IRubyObject step, final Block block) {
        String method = "step";
        if (!block.isGiven()) {
            return stepEnumeratorize(context, step, method);
        }

        step = checkStepDomain(context, step, method);

        return stepCommon(context, step, block);
    }

    private IRubyObject checkStepDomain(ThreadContext context, IRubyObject step, String method) {
        if (!(step instanceof RubyNumeric)) step = step.convertToInteger("to_int");
        if (((RubyNumeric) step).isNegative()) throw argumentError(context, method + " can't be negative");
        if (((RubyNumeric) step).isZero()) throw argumentError(context, method + " can't be 0");

        return step;
    }

    private IRubyObject stepEnumeratorize(ThreadContext context, IRubyObject step, String method) {
        if (!step.isNil() && !(step instanceof RubyNumeric)) step = step.convertToInteger("to_int");
        if ((step instanceof RubyNumeric) && ((RubyNumeric) step).isZero()) throw argumentError(context, "step can't be 0");

        if ((begin instanceof RubyNumeric && (end.isNil() || end instanceof RubyNumeric)) ||
                (end instanceof RubyNumeric && begin.isNil())) {

            return RubyArithmeticSequence.newArithmeticSequence(
                    context,
                    this,
                    method,
                    !step.isNil() ? new IRubyObject[]{step} : null,
                    begin,
                    end,
                    !step.isNil() ? step : RubyFixnum.one(context.runtime),
                    isExclusive ? context.tru : context.fals);
        }

        return !step.isNil() ?
                enumeratorizeWithSize(context, this, method, new IRubyObject[]{step}, RubyRange::stepSize) :
                enumeratorizeWithSize(context, this, method, RubyRange::stepSize);
    }

    @JRubyMethod(name = "%")
    public IRubyObject op_mod(final ThreadContext context, IRubyObject step) {
        return stepEnumeratorize(context, step, "%");
    }

    private IRubyObject stepCommon(ThreadContext context, IRubyObject step, Block block) {
        Ruby runtime = context.runtime;
        if (begin instanceof RubyFixnum && end.isNil() && step instanceof RubyFixnum) {
            long i = begin.convertToInteger().getLongValue();
            long unit = step.convertToInteger().getLongValue();
            while (i < Long.MAX_VALUE) {
                block.yield(context, asFixnum(context, i));
                i += unit;
            }
            IRubyObject b = asFixnum(context, i);
            for (;; b = ((RubyInteger) b).op_plus(context, step)) {
                block.yield(context, b);
            }
        } else if (begin instanceof RubyFixnum && end instanceof RubyFixnum && step instanceof RubyFixnum) {
            fixnumStep(context, ((RubyFixnum) step).getLongValue(), block);
        } else if (begin instanceof RubyFloat || end instanceof RubyFloat || step instanceof RubyFloat) {
            RubyNumeric.floatStep(context, runtime, begin, end, step, isExclusive, isEndless, block);
        } else if (begin instanceof RubySymbol && (end.isNil() || end instanceof RubySymbol)) { /* symbols are special */
            RubyString b = begin.asString();
            SymbolStepBlockCallBack callback = new SymbolStepBlockCallBack(block, RubyFixnum.one(runtime), step);
            Block blockCallback = CallBlock.newCallClosure(context, this, Signature.ONE_ARGUMENT, callback);
            if (end.isNil()) {
                b.uptoEndless(context, blockCallback);
            } else {
                b.uptoCommon(context, end.asString(), isExclusive, blockCallback);
            }
        } else if (begin instanceof RubyNumeric
                || !checkToInteger(context, begin).isNil()
                || !checkToInteger(context, end).isNil()) {
            numericStep(context, step, block);
        } else {
            IRubyObject tmp = begin.checkStringType();
            if (!tmp.isNil()) {
                StepBlockCallBack callback = new StepBlockCallBack(block, RubyFixnum.one(runtime), step);
                Block blockCallback = CallBlock.newCallClosure(context, this, Signature.ONE_ARGUMENT, callback);
                if (end.isNil()) {
                    ((RubyString) tmp).uptoEndless(context, blockCallback);
                } else {
                    ((RubyString) tmp).uptoCommon(context, end, isExclusive, blockCallback);
                }
            } else {
                if (!begin.respondsTo("succ")) throw typeError(context, "can't iterate from ", begin, "");

                // range_each_func(range, step_i, b, e, args);
                rangeEach(context, new StepBlockCallBack(block, RubyFixnum.one(runtime), step));
            }
        }
        return this;
    }

    private void fixnumStep(ThreadContext context, long step, Block block) {
        // We must avoid integer overflows.
        // Any method calling this method must ensure that "step" is greater than 0.
        long to = ((RubyFixnum) end).getLongValue();
        if (isExclusive) {
            if (to == Long.MIN_VALUE) return;
            to--;
        }
        long tov = Long.MAX_VALUE - step;
        if (to < tov) tov = to;

        long i;
        for (i = ((RubyFixnum) begin).getLongValue(); i <= tov; i += step) {
            block.yield(context, asFixnum(context, i));
        }
        if (i <= to) block.yield(context, asFixnum(context, i));
    }

    private void numericStep(ThreadContext context, IRubyObject step, Block block) {
        final String method = isExclusive ? "<" : "<=";
        IRubyObject beg = begin;
        long i = 0;
        while (beg.callMethod(context, method, end).isTrue()) {
            block.yield(context, beg);
            i++;
            beg = begin.callMethod(context, "+", asFixnum(context, i).callMethod(context, "*", step));
        }
    }

    /**
     * A size method suitable for lambda method reference implementation of {@link SizeFn#size(ThreadContext, IRubyObject, IRubyObject[])}
     *
     * @see SizeFn#size(ThreadContext, IRubyObject, IRubyObject[])
     */
    private static IRubyObject size(ThreadContext ctx, RubyRange recv, IRubyObject[] args) {
        return recv.size(ctx);
    }

    /**
     * A step size method suitable for lambda method reference implementation of {@link SizeFn#size(ThreadContext, IRubyObject, IRubyObject[])}
     *
     * @see SizeFn#size(ThreadContext, IRubyObject, IRubyObject[])
     */
    private static IRubyObject stepSize(ThreadContext context, RubyRange self, IRubyObject[] args) {
        IRubyObject begin = self.begin;
        IRubyObject end = self.end;
        IRubyObject step;

        if (args != null && args.length > 0) {
            step = args[0];
            if (!(step instanceof RubyNumeric)) step = step.convertToInteger();
        } else {
            step = asFixnum(context, 1);
        }

        var zero = asFixnum(context, 0);
        if (step.callMethod(context, "<", zero).isTrue()) throw argumentError(context, "step can't be negative");
        if (!step.callMethod(context, ">", zero).isTrue()) throw argumentError(context, "step can't be 0");

        if (begin instanceof RubyNumeric && end instanceof RubyNumeric) {
            return intervalStepSize(context, begin, end, step, self.isExclusive);
        }

        return context.nil;
    }

    // framed for invokeSuper
    @JRubyMethod(name = {"include?", "member?"}, frame = true)
    public IRubyObject include_p(ThreadContext context, final IRubyObject obj) {
        IRubyObject result = includeCommon(context, obj, false);
        if (result != UNDEF) return result;
        return Helpers.invokeSuper(context, this, obj, Block.NULL_BLOCK);
    }

    // MRI: range_include_internal
    private IRubyObject includeCommon(ThreadContext context, final IRubyObject val, boolean useStringCover) {
        final Ruby runtime = context.runtime;

        boolean iterable = begin instanceof RubyNumeric || end instanceof RubyNumeric ||
                linearObject(context, begin) || linearObject(context, end);

        JavaSites.RangeSites sites = sites(context);
        JavaSites.CheckedSites to_int_checked = sites.to_int_checked;
        if (iterable
                || !TypeConverter.convertToTypeWithCheck(context, begin, runtime.getInteger(), to_int_checked).isNil()
                || !TypeConverter.convertToTypeWithCheck(context, end, runtime.getInteger(), to_int_checked).isNil()) {
            return asBoolean(context, rangeIncludes(context, val));
        } else if (begin instanceof RubyString || end instanceof RubyString) {
            if (begin instanceof RubyString && end instanceof RubyString) {
                if (useStringCover) {
                    return cover_p(context, val);
                } else {
                    return RubyString.includeRange(context, (RubyString) begin, (RubyString) end, val, isExclusive);
                }
            } else if (begin.isNil()) {
                IRubyObject r = sites.op_cmp.call(context, val, val, end);
                if (r.isNil()) return context.fals;
                if (RubyComparable.cmpint(context, sites.op_gt, sites.op_lt, r, val, end) <= 0) return context.tru;
                return context.fals;
            } else if (end.isNil()) {
                IRubyObject r = sites.op_cmp.call(context, begin, begin, val);
                if (r.isNil()) return context.fals;
                if (RubyComparable.cmpint(context, sites.op_gt, sites.op_lt, r, begin, val) <= 0) return context.tru;
                return context.fals;
            }
        }

        return UNDEF;
    }

    private static boolean discreteObject(ThreadContext context, IRubyObject obj) {
        return sites(context).respond_to_succ.respondsTo(context, obj, obj, false);
    }

    private static boolean linearObject(ThreadContext context, IRubyObject obj) {
        if (obj instanceof RubyFixnum || obj instanceof RubyFloat) return true;
//        if (SPECIAL_CONST_P(obj)) return FALSE;
        if (obj instanceof RubyBignum) return true;
        if (obj instanceof RubyNumeric) return true;
        if (obj instanceof RubyTime) return true;
        return false;
    }

    @JRubyMethod(name = "===")
    public IRubyObject eqq_p(ThreadContext context, IRubyObject obj) {
        IRubyObject result = includeCommon(context, obj, true);
        if (result != UNDEF) return result;
        return asBoolean(context, rangeIncludes(context, obj));
    }

    @JRubyMethod(name = "cover?")
    public RubyBoolean cover_p(ThreadContext context, IRubyObject obj) {
        return asBoolean(context,
                obj instanceof RubyRange range ? coverRange(context, range) : rangeIncludes(context, obj));
    }

    // MRI: r_cover_p
    private boolean rangeIncludes(ThreadContext context, IRubyObject val) {
        if (isBeginless || rangeLess(context, begin, val) <= 0) {
            int excl = isExclusive ? 1 : 0;
            if (isEndless || rangeLess(context, val, end) <= -excl) {
                return true;
            }
        }

        return false;
    }


    @JRubyMethod(frame = true)
    public IRubyObject min(ThreadContext context, Block block) {
        return min(context, null, block);
    }

    @JRubyMethod(frame = true)
    public IRubyObject min(ThreadContext context, IRubyObject arg, Block block) {
        if (begin.isNil()) throw rangeError(context, "cannot get the minimum of beginless range");

        if (block.isGiven()) {
            if (end.isNil()) throw rangeError(context, "cannot get the minimum of endless range with custom comparison method");

            return arg != null ? Helpers.invokeSuper(context, this, arg, block) : Helpers.invokeSuper(context, this, block);
        }
        if (arg != null) return first(context, arg);

        int cmp = isEndless ? -1 : RubyComparable.cmpint(context, invokedynamic(context, begin, MethodNames.OP_CMP, end), begin, end);
        return cmp > 0 || cmp == 0 && isExclusive ? context.nil : begin;
    }

    @JRubyMethod(frame = true)
    public IRubyObject max(ThreadContext context, Block block) {
        if (isEndless) throw rangeError(context, "cannot get the maximum of endless range");

        if (block.isGiven() || isExclusive && !(end instanceof RubyNumeric)) {
            if (isBeginless) {
                throw rangeError(context, "cannot get the maximum of beginless range with custom comparison method");
            }
            return Helpers.invokeSuper(context, this, block);
        }

        int cmp = isBeginless ? -1 : RubyComparable.cmpint(context, invokedynamic(context, begin, MethodNames.OP_CMP, end), begin, end);
        if (cmp > 0) return context.nil;

        if (isExclusive) {
            if (!(end instanceof RubyInteger)) throw typeError(context, "cannot exclude non Integer end value");

            if (cmp == 0) return context.nil;

            if (!(begin instanceof RubyInteger)) throw typeError(context, "cannot exclude end value with non Integer begin value");

            return end instanceof RubyFixnum fixnum ?
                    asFixnum(context, fixnum.getLongValue() - 1) :
                    end.callMethod(context, "-", RubyFixnum.one(context.runtime));
        }

        return end;
    }

    @JRubyMethod(frame = true)
    public IRubyObject max(ThreadContext context, IRubyObject arg, Block block) {
        if (isEndless) throw rangeError(context, "cannot get the maximum element of endless range");
        return Helpers.invokeSuper(context, this, arg, block);
    }

    @JRubyMethod
    public IRubyObject first(ThreadContext context) {
        return first(context, null);
    }

    @JRubyMethod @JRubyAPI
    public IRubyObject begin(ThreadContext context) {
        return begin;
    }

    @JRubyMethod
    public IRubyObject first(ThreadContext context, IRubyObject arg) {
        if (isBeginless) throw rangeError(context, "cannot get the first element of beginless range");

        if (arg == null) return begin;

        final int num = RubyNumeric.num2int(arg);
        if (num < 0) throw argumentError(context, "negative array size (or size too big)");

        // TODO (CON): this could be packed if we know there are at least num elements in range
        final var result = newRawArray(context, num);
        try {
            RubyEnumerable.callEach(context, sites(context).each, this, Signature.ONE_ARGUMENT, new BlockCallback() {
                int n = num;

                public IRubyObject call(ThreadContext ctx, IRubyObject[] largs, Block blk) {
                    return call(ctx, largs[0], blk);
                }

                @Override
                public IRubyObject call(ThreadContext ctx, IRubyObject larg, Block blk) {
                    if (n-- <= 0) throw JumpException.SPECIAL_JUMP;

                    result.append(context, larg);
                    return ctx.nil;
                }
            });
        } catch (JumpException.SpecialJump sj) {
        }
        return result.finishRawArray(context);
    }

    @JRubyMethod
    public IRubyObject count(ThreadContext context, Block block) {
        if (isBeginless || isEndless) return asFloat(context, RubyFloat.INFINITY);

        if (begin instanceof RubyInteger) {
            IRubyObject size = size(context);
            if (!size.isNil()) return size;
        }

        return RubyEnumerable.count(context, this, block);
    }

    @JRubyMethod
    public IRubyObject minmax(ThreadContext context, Block block) {
        if (block.isGiven()) return Helpers.invokeSuper(context, this, context.runtime.getRange(), "minmax", NULL_ARRAY, block);

        return newArray(context, callMethod("min"), callMethod("max"));
    }

    @JRubyMethod
    public IRubyObject last(ThreadContext context) {
        if (isEndless) throw rangeError(context, "cannot get the last element of endless range");
        return end;
    }

    @JRubyMethod @JRubyAPI
    public IRubyObject end(ThreadContext context) {
        return end;
    }

    @JRubyMethod
    public IRubyObject last(ThreadContext context, IRubyObject arg) {
        if (isEndless) throw rangeError(context, "cannot get the last element of endless range");

        if (begin instanceof RubyInteger && end instanceof RubyInteger
            && getMetaClass().checkMethodBasicDefinition("each")) {
                return intRangeLast(context, arg);
        }

        return ((RubyArray) RubyKernel.new_array(context, this, this)).last(context, arg);
    }

    // MRI rb_int_range_last
    private RubyArray intRangeLast(ThreadContext context, IRubyObject arg) {
        IRubyObject one = asFixnum(context, 1);
        IRubyObject len1, len, nv, b;

        len1 = ((RubyInteger)end).op_minus(context, begin);

        if (isExclusive) {
            end = ((RubyInteger)end).op_minus(context, one);
            len = len1;
        } else {
            len = ((RubyInteger)len1).op_plus(context, one);
        }

        if (((RubyInteger)len).isZero() || Numeric.f_negative_p(context, (RubyInteger)len)) {
            return RubyArray.newEmptyArray(context.runtime);
        }

        long n = numericToLong(context, arg);
        if (n < 0) throw argumentError(context, "negative array size");

        nv = asFixnum(context, n);
        if (Numeric.f_gt_p(context, nv, len)) {
             nv = len;
             n = numericToLong(context, nv);
        }

        RubyArray<?> array = newRawArray(context, n);
        b = ((RubyInteger)end).op_minus(context, nv);
        while (n > 0) {
            b = ((RubyInteger)b).op_plus(context, one);
            array.append(context, b);
            n--;
        }

        return array.finishRawArray(context);
    }

    @JRubyMethod
    public IRubyObject size(ThreadContext context) {
        if (begin instanceof RubyInteger) {
            if (end instanceof RubyNumeric) {
                return RubyNumeric.intervalStepSize(context, begin, end, RubyFixnum.one(context.runtime), isExclusive);
            }
            if (end.isNil()) {
                return dbl2num(context.runtime, Double.POSITIVE_INFINITY);
            }
        }

        if (!discreteObject(begin)) {
            throw typeError(context, str(context.runtime, "can't iterate from ", types(context, begin.getMetaClass())));
        }

        return context.nil;
    }

    private boolean discreteObject(IRubyObject object) {
        return object.respondsTo("succ");
    }

    public final boolean isExcludeEnd() {
        return isExclusive;
    }

    private static final ObjectMarshal RANGE_MARSHAL = new ObjectMarshal() {
        @Override
        public void marshalTo(Ruby runtime, Object obj, RubyClass type,
                MarshalStream marshalStream) throws IOException {
            RubyRange range = (RubyRange) obj;

            marshalStream.registerLinkTarget(range);
            List<Variable<Object>> attrs = range.getMarshalVariableList();

            attrs.add(new VariableEntry<>("excl", range.isExclusive ? runtime.getTrue() : runtime.getFalse()));
            attrs.add(new VariableEntry<>("begin", range.begin));
            attrs.add(new VariableEntry<>("end", range.end));

            marshalStream.dumpVariables(attrs);
        }

        @Override
        public void marshalTo(Object obj, RubyClass type,
                              NewMarshal marshalStream, ThreadContext context, NewMarshal.RubyOutputStream out) {
            RubyRange range = (RubyRange) obj;

            marshalStream.registerLinkTarget(range);

            marshalStream.dumpVariables(context, out, range, 3, (marshal, c, o, v, receiver) -> {
                receiver.receive(marshal, c, o, "excl", v.isExclusive ? c.tru : c.fals);
                receiver.receive(marshal, c, o, "begin", v.begin);
                receiver.receive(marshal, c, o, "end", v.end);
            });
        }

        @Override
        public Object unmarshalFrom(Ruby runtime, RubyClass type, UnmarshalStream input) throws IOException {
            var context = runtime.getCurrentContext();
            RubyRange range = (RubyRange) input.entry(type.allocate());

            input.ivar(null, range, null);

            IRubyObject excl = (IRubyObject) range.removeInternalVariable("excl");
            IRubyObject begin = (IRubyObject) range.removeInternalVariable("begin");
            IRubyObject end = (IRubyObject) range.removeInternalVariable("end");

            // try old names as well
            if (begin == null) begin = (IRubyObject) range.removeInternalVariable("begini");
            if (end == null) end = (IRubyObject) range.removeInternalVariable("endi");

            if (begin == null || end == null || excl == null) throw argumentError(context, "bad value for range");

            range.init(context, begin, end, excl.isTrue());
            return range;
        }
    };

    /**
     * Given a range-line object that response to "begin", "end", construct a proper range
     * by calling those methods and "exclude_end?" with the given call sites.
     *
     * @param context current context
     * @param rangeLike range-like object
     * @param beginSite "begin" call site
     * @param endSite "end" call site
     * @param excludeEndSite "exclude_end?" call site
     * @return a proper Range based on the results of calling those methods
     */
    public static RubyRange rangeFromRangeLike(ThreadContext context, IRubyObject rangeLike, CallSite beginSite, CallSite endSite, CallSite excludeEndSite) {
        IRubyObject begin = beginSite.call(context, rangeLike, rangeLike);
        IRubyObject end   = endSite.call(context, rangeLike, rangeLike);
        IRubyObject excl  = excludeEndSite.call(context, rangeLike, rangeLike);
        return newRange(context, begin, end, excl.isTrue());
    }

    /**
     * Return true if the given object responds to "begin" and "end" methods.
     *
     * @param context current context
     * @param obj possibly range-like object
     * @param respond_to_begin respond_to? site for begin
     * @param respond_to_end respond_to? site for end
     * @return
     */
    public static boolean isRangeLike(ThreadContext context, IRubyObject obj, RespondToCallSite respond_to_begin, RespondToCallSite respond_to_end) {
        return respond_to_begin.respondsTo(context, obj, obj) &&
                respond_to_end.respondsTo(context, obj, obj);
    }

    /**
     * Return true if the given object responds to "begin", "end" and "exclude_end?" methods.
     *
     * @param context current context
     * @param obj possibly range-like object
     * @param begin_checked checked site for begin
     * @param end_checked checked site for end
     * @param exclude_end_checked checked site for exclude_end?
     * @return
     */
    public static boolean isRangeLike(ThreadContext context, IRubyObject obj, JavaSites.CheckedSites begin_checked, JavaSites.CheckedSites end_checked, JavaSites.CheckedSites exclude_end_checked) {
        if (obj instanceof RubyArithmeticSequence) return false;
        return (obj.checkCallMethod(context, begin_checked) != null) &&
                (obj.checkCallMethod(context, end_checked) != null) &&
                (obj.checkCallMethod(context, exclude_end_checked) != null);
    }

    // MRI: rb_range_beg_len
    public static IRubyObject rangeBeginLength(ThreadContext context, IRubyObject range, int len, int[] begLen, int err) {
        JavaSites.RangeSites sites = sites(context);

        if (!RubyRange.isRangeLike(context, range, sites.respond_to_begin, sites.respond_to_end)) return context.fals;

        IRubyObject _beg = sites.begin.call(context, range, range);
        IRubyObject _end = sites.end.call(context, range, range);
        boolean excludeEnd = sites.exclude_end.call(context, range, range).isTrue();
        int beg = _beg.isNil() ? 0 : _beg.convertToInteger().getIntValue();
        int end = _end.isNil() ? -1 :_end.convertToInteger().getIntValue();
        int origBeg = beg;
        int origEnd = end;

        if (beg < 0) {
            beg += len;
            if (beg < 0) {
                return rangeBeginLengthError(context, origBeg, origEnd, excludeEnd, err);
            }
        }

        if (end < 0) {
            end += len;
        }

        if (!excludeEnd) end++;

        if (err == 0 || err == 2) { // CON: ???
            if (beg > len) return rangeBeginLengthError(context, origBeg, origEnd, excludeEnd, err);
            if (end > len) end = len;
        }

        len = end - beg;
        if (len < 0) len = 0;

        begLen[0] = beg;
        begLen[1] = len;

        return context.tru;
    }

    private static IRubyObject rangeBeginLengthError(ThreadContext context, int beg, int end, boolean excludeEnd, int err) {
        if (err != 0) throw rangeError(context, beg + ".." + (excludeEnd ? "." : "") + end + " out of range");
        return context.nil;
    }

    public static class RangeLike {
        final IRubyObject begin;
        final IRubyObject end;
        final boolean excl;

        RangeLike(IRubyObject begin, IRubyObject end, boolean excl) {
            this.begin = begin;
            this.end = end;
            this.excl = excl;
        }

        IRubyObject getRange(ThreadContext context) {
            return Helpers.invoke(context, end, "-", begin);
        }
    }

    // MRI: rb_range_values
    public static RangeLike rangeValues(ThreadContext context, IRubyObject range) {
        if (range instanceof RubyRange vrange) {
            return new RangeLike(vrange.begin(context), vrange.end(context), vrange.isExcludeEnd());
        } else if (range instanceof RubyArithmeticSequence) {
            return null;
        } else if (range.respondsTo("begin") && range.respondsTo("end") && range.respondsTo("exclude_end?")) {
            return new RangeLike(Helpers.invoke(context, range, "begin"), Helpers.invoke(context, range, "end"),
                    Helpers.invoke(context, range, "exclude_end?").isTrue());
        }

        return null;
    }

    public static class BSearch {
        @JRubyMethod(meta = true)
        public static IRubyObject double_to_long_bits(ThreadContext context, IRubyObject bsearch, IRubyObject flote) {
            return flote instanceof RubyFixnum value ?
                    asFixnum(context, Double.doubleToLongBits(value.getDoubleValue())) :
                    asFixnum(context, Double.doubleToLongBits(((RubyFloat) flote).getDoubleValue()));
        }

        @JRubyMethod(meta = true)
        public static IRubyObject long_bits_to_double(ThreadContext context, IRubyObject bsearch, IRubyObject fixnum) {
            return asFloat(context, Double.longBitsToDouble(((RubyFixnum) fixnum).getLongValue()));
        }

        @JRubyMethod(meta = true)
        public static IRubyObject abs(ThreadContext context, IRubyObject bsearch, IRubyObject flote) {
            return asFloat(context, Math.abs(((RubyFloat) flote).getDoubleValue()));
        }
    }

    private static JavaSites.RangeSites sites(ThreadContext context) {
        return context.sites.Range;
    }
}

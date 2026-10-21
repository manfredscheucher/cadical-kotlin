package org.bytefred.ksat.cadical.full

import kotlin.math.abs
import org.bytefred.ksat.cadical.IntArrayList

/*
 * extend.cpp (CaDiCaL 2.1.3): pushing clauses and witnesses on the extension stack, model
 * extension (solution reconstruction), witness traversal and 'conclude_sat'.
 *
 * Extension stack layout per weakened clause (external literals, 'vector<int>'):
 *   0, witness literals..., 0, higher id bits, lower id bits, 0, clause literals...
 * Iterators into 'extension' are Int indices.
 *
 * 'id' bits: upstream computes 'higher_bits = static_cast<int> (id << 32)', which keeps the
 * low 32 bits of 'id << 32', i.e. always 0, and 'lower_bits = id & (2^32 - 1)'; both are
 * then stored as 'int' (bit pattern). Ported exactly, including the 'always 0'.
 *
 * Dropped as PORTING.md says: LOG, PHASE, START/STOP; the 'updated' / 'flipped' counters
 * only feed PHASE (#ifndef QUIET).
 */

internal fun External.pushZeroOnExtensionStack() {
    extension.add(0)
}

internal fun External.pushIdOnExtensionStack(id: Long) {
    val higherBits: Int = (id shl 32).toInt()
    val lowerBits: Int = (id and ((1L shl 32) - 1)).toInt()
    extension.add(higherBits)
    extension.add(lowerBits)
}

internal fun External.pushClauseLiteralOnExtensionStack(ilit: Int) {
    check(ilit != 0)
    val elit = internal.externalize(ilit)
    check(elit != 0)
    extension.add(elit)
}

internal fun External.pushWitnessLiteralOnExtensionStack(ilit: Int) {
    check(ilit != 0)
    val elit = internal.externalize(ilit)
    check(elit != 0)
    extension.add(elit)
    if (marked(witness, elit)) return
    mark(witness, elit)
}

// The extension stack allows to reconstruct a satisfying assignment for the
// original formula after removing eliminated clauses.  This was pioneered
// by Niklas Soerensson in MiniSAT and for instance is described in our
// inprocessing paper, published at IJCAR'12.  This first function adds a
// clause to this stack.  First the blocking or eliminated literal is added,
// and then the rest of the clause.

internal fun External.pushClauseOnExtensionStack(c: Clause) {
    internal.stats.weakened++
    internal.stats.weakenedlen += c.size
    pushZeroOnExtensionStack()
    pushIdOnExtensionStack(c.id)
    pushZeroOnExtensionStack()
    for (k in 0 until c.size) pushClauseLiteralOnExtensionStack(c.literals[k])
}

// Upstream names the second parameter 'pivot' in the definition.
internal fun External.pushClauseOnExtensionStack(c: Clause, witness: Int) {
    val pivot = witness
    pushZeroOnExtensionStack()
    pushWitnessLiteralOnExtensionStack(pivot)
    pushClauseOnExtensionStack(c)
}

// Upstream names the second parameter 'pivot' in the definition.
internal fun External.pushBinaryClauseOnExtensionStack(id: Long, witness: Int, other: Int) {
    val pivot = witness
    internal.stats.weakened++
    internal.stats.weakenedlen += 2
    pushZeroOnExtensionStack()
    pushWitnessLiteralOnExtensionStack(pivot)
    pushZeroOnExtensionStack()
    pushIdOnExtensionStack(id)
    pushZeroOnExtensionStack()
    pushClauseLiteralOnExtensionStack(pivot)
    pushClauseLiteralOnExtensionStack(other)
}

/*------------------------------------------------------------------------*/

internal fun External.pushExternalClauseAndWitnessOnExtensionStack(clause: IntArrayList, witness: IntArrayList, id: Long) {
    val c = clause
    val w = witness
    check(id != 0L)
    extension.add(0)
    for (k in 0 until w.size) {
        val elit = w[k]
        check(elit != Int.MIN_VALUE)
        init(abs(elit))
        extension.add(elit)
        mark(this.witness, elit)
    }
    extension.add(0)
    val higherBits: Int = (id shl 32).toInt()
    val lowerBits: Int = (id and ((1L shl 32) - 1)).toInt()
    extension.add(higherBits)
    extension.add(lowerBits)
    extension.add(0)
    for (k in 0 until c.size) {
        val elit = c[k]
        check(elit != Int.MIN_VALUE)
        init(abs(elit))
        extension.add(elit)
    }
}

/*------------------------------------------------------------------------*/

// This is the actual extension process. It goes backward over the clauses
// on the extension stack and flips the assignment of one of the blocking
// literals in the conditional autarky stored before the clause.  In the
// original algorithm for witness construction for variable elimination and
// blocked clause removal the conditional autarky consists of a single
// literal from the removed clause, while in general the autarky witness can
// contain an arbitrary set of literals.  We are using the more general
// witness reconstruction here which for instance would also work for
// super-blocked or set-blocked clauses.

internal fun External.extend() {

    check(!extended) { "already extended" }
    internal.stats.extensions++

    for (i in 1..maxVar) {
        val ilit = e2i[i]
        if (ilit == 0) continue
        if (i >= vals.size) vals.resize(i + 1, false)
        vals[i] = internal.value(ilit) > 0
    }
    val begin = 0
    var i = extension.size
    while (i != begin) {
        var satisfied = false
        var lit: Int
        check(i != begin)
        while (true) {
            lit = extension[--i]
            if (lit == 0) break
            if (satisfied) continue
            if (ival(lit) == lit) satisfied = true
            check(i != begin)
        }
        check(i != begin)
        // LOG ("id=...", *i, *(i - 1)) dropped.
        check(extension[i] != 0 || extension[i - 1] != 0)
        --i
        check(i != begin)
        --i
        check(i != begin)
        check(extension[i] == 0)
        --i
        check(i != begin)
        if (satisfied) {
            while (extension[--i] != 0) check(i != begin)
        } else {
            while (true) {
                lit = extension[--i]
                if (lit == 0) break
                val tmp = ival(lit) // not 'signed char'!!!
                if (tmp != lit) {
                    check(lit != 0)
                    check(lit != Int.MIN_VALUE)
                    val idx = abs(lit)
                    if (idx >= vals.size) vals.resize(idx + 1, false)
                    vals[idx] = !vals[idx]
                    internal.stats.extended++
                }
                check(i != begin)
            }
        }
    }
    extended = true
}

/*------------------------------------------------------------------------*/

internal fun External.traverseWitnessesBackward(it: WitnessIterator): Boolean {
    if (internal.unsat) return true
    val clause = ArrayList<Int>()
    val witness = ArrayList<Int>()
    val begin = 0
    var i = extension.size
    while (i != begin) {
        var lit: Int
        while (true) {
            lit = extension[--i]
            if (lit == 0) break
            clause.add(lit)
        }
        check(lit == 0)
        --i
        // ((uint64_t) *(i - 1) << 32) + static_cast<uint64_t> (*i): 'int' to 'uint64_t'
        // sign-extends, as 'toLong ()' does; the Long sum wraps as uint64_t.
        val id: Long = (extension[i - 1].toLong() shl 32) + extension[i].toLong()
        check(id != 0L)
        i -= 2
        check(extension[i] == 0)
        check(i != begin)
        while (true) {
            lit = extension[--i]
            if (lit == 0) break
            witness.add(lit)
        }
        clause.reverse()
        witness.reverse()
        if (!it.witness(clause, witness, id)) return false
        clause.clear()
        witness.clear()
    }
    return true
}

internal fun External.traverseWitnessesForward(it: WitnessIterator): Boolean {
    if (internal.unsat) return true
    val clause = ArrayList<Int>()
    val witness = ArrayList<Int>()
    val end = extension.size
    var i = 0
    if (i != end) {
        var lit = extension[i++]
        do {
            check(lit == 0)
            while (true) {
                lit = extension[i++]
                if (lit == 0) break
                witness.add(lit)
            }
            check(lit == 0)
            check(i != end)
            check(extension[i] == 0)
            val id: Long = (extension[i].toLong() shl 32) + extension[i + 1].toLong()
            check(id != 0L) // 'assert (id > 0)' on uint64_t
            i += 3
            check(extension[i] != 0)
            check(i != end)
            while (i != end) {
                lit = extension[i++]
                if (lit == 0) break
                clause.add(lit)
            }
            if (!it.witness(clause, witness, id)) return false
            clause.clear()
            witness.clear()
        } while (i != end)
    }
    return true
}

/*------------------------------------------------------------------------*/

internal fun External.concludeSat() {
    val proof = internal.proof
    if (proof == null || concluded) return
    concluded = true
    if (!extended) extend()
    val model = IntArrayList()
    for (idx in 1..maxVar) {
        val lit = ival(idx)
        model.add(lit)
    }
    proof.concludeSat(model)
}

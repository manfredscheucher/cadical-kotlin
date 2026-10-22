package org.bytefred.ksat.cadical.full

/*
 * proof.cpp: the 'Internal::' functions (connecting proof tracers). The members of
 * 'class Proof' are in ProofHpp.kt (PORTING.md: a class cannot be split over files).
 *
 * 'DeferDeletePtr' (deleting the checker if 'connect' throws) is dropped (garbage collected).
 */

/*------------------------------------------------------------------------*/

// Enable proof logging and checking by allocating a 'Proof' object.

internal fun Internal.newProofOnDemand() {
    if (proof == null) {
        proof = Proof(this)
        setupLratBuilder()
    }
}

internal fun Internal.setupLratBuilder() {
    if (lratbuilder != null) return
    if (opts.externallrat != 0) {
        val lb = LratBuilder(this)
        lratbuilder = lb
        proof!!.connect(lb)
    }
}

internal fun Internal.resizeUnitClausesIdx() {
    val newVsize = if (vsize != 0) 2 * vsize else 1 + maxVar
    unitClausesIdx = unitClausesIdx.resized(2 * newVsize, 0L)
}

internal fun Internal.forceLrat() {
    if (lrat || lratbuilder != null) return
    lrat = true
}

internal fun Internal.connectProofTracer(tracer: Tracer, antecedents: Boolean, finalizeClauses: Boolean = false) {
    newProofOnDemand()
    if (antecedents) forceLrat()
    if (finalizeClauses) frat = true
    resizeUnitClausesIdx()
    proof!!.connect(tracer)
    tracers.add(tracer)
}

internal fun Internal.connectProofTracer(tracer: InternalTracer, antecedents: Boolean, finalizeClauses: Boolean = false) {
    newProofOnDemand()
    if (antecedents) forceLrat()
    if (finalizeClauses) frat = true
    resizeUnitClausesIdx()
    tracer.connectInternal(this)
    proof!!.connect(tracer)
    tracers.add(tracer)
}

internal fun Internal.connectProofTracer(tracer: StatTracer, antecedents: Boolean, finalizeClauses: Boolean = false) {
    newProofOnDemand()
    if (antecedents) forceLrat()
    if (finalizeClauses) frat = true
    resizeUnitClausesIdx()
    tracer.connectInternal(this)
    proof!!.connect(tracer)
    statTracers.add(tracer)
}

internal fun Internal.connectProofTracer(tracer: FileTracer, antecedents: Boolean, finalizeClauses: Boolean = false) {
    newProofOnDemand()
    if (antecedents) forceLrat()
    if (finalizeClauses) frat = true
    resizeUnitClausesIdx()
    tracer.connectInternal(this)
    proof!!.connect(tracer)
    fileTracers.add(tracer)
}

/** 'std::find' on a vector of pointers: index of the first element identical to [x], or -1. */
private fun <T> ArrayList<T>.findIdentical(x: T): Int {
    for (k in 0 until size) if (this[k] === x) return k
    return -1
}

internal fun Internal.disconnectProofTracer(tracer: Tracer): Boolean {
    val it = tracers.findIdentical(tracer)
    if (it != -1) {
        tracers.removeAt(it)
        check(proof != null) { "tracer connected without proof" }
        proof!!.disconnect(tracer)
        return true
    }
    return false
}

internal fun Internal.disconnectProofTracer(tracer: StatTracer): Boolean {
    val it = statTracers.findIdentical(tracer)
    if (it != -1) {
        statTracers.removeAt(it)
        check(proof != null) { "tracer connected without proof" }
        proof!!.disconnect(tracer)
        return true
    }
    return false
}

internal fun Internal.disconnectProofTracer(tracer: FileTracer): Boolean {
    val it = fileTracers.findIdentical(tracer)
    if (it != -1) {
        fileTracers.removeAt(it)
        check(proof != null) { "tracer connected without proof" }
        proof!!.disconnect(tracer)
        return true
    }
    return false
}

// 'Proof::disconnect' is a member of 'Proof' (ProofHpp.kt).

// Enable proof tracing.

internal fun Internal.trace(file: File) {
    if (opts.veripb != 0) {
        val antecedents = opts.veripb == 1 || opts.veripb == 2
        val deletions = opts.veripb == 2 || opts.veripb == 4
        val ft: FileTracer = VeripbTracer(this, file, opts.binary != 0, antecedents, deletions)
        connectProofTracer(ft, antecedents)
    } else if (opts.frat != 0) {
        val antecedents = opts.frat == 1
        resizeUnitClausesIdx()
        val ft: FileTracer = FratTracer(this, file, opts.binary != 0, opts.frat == 1)
        connectProofTracer(ft, antecedents, true)
    } else if (opts.lrat != 0) {
        val ft: FileTracer = LratTracer(this, file, opts.binary != 0)
        connectProofTracer(ft, true)
    } else if (opts.idrup != 0) {
        val ft: FileTracer = IdrupTracer(this, file, opts.binary != 0)
        connectProofTracer(ft, true)
    } else if (opts.lidrup != 0) {
        val ft: FileTracer = LidrupTracer(this, file, opts.binary != 0)
        connectProofTracer(ft, true)
    } else {
        val ft: FileTracer = DratTracer(this, file, opts.binary != 0)
        connectProofTracer(ft, false)
    }
}

// Enable proof checking.

internal fun Internal.check() {
    newProofOnDemand()
    if (opts.checkproof > 1) {
        val lratchecker: StatTracer = LratChecker(this)
        forceLrat()
        frat = true
        resizeUnitClausesIdx()
        proof!!.connect(lratchecker)
        statTracers.add(lratchecker)
    }
    if (opts.checkproof == 1 || opts.checkproof == 3) {
        val checker: StatTracer = Checker(this)
        proof!!.connect(checker)
        statTracers.add(checker)
    }
}

// We want to close a proof trace and stop checking as soon we are done.

internal fun Internal.closeTrace(stats: Boolean = false) {
    for (tracer in fileTracers) tracer.close(stats)
}

// We can flush a proof trace file before actually closing it.

internal fun Internal.flushTrace(stats: Boolean = false) {
    for (tracer in fileTracers) tracer.flush(stats)
}

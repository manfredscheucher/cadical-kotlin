package org.bytefred.ksat.cadical.full

/*
 * arena.hpp plus arena.cpp: memory arena for the moving garbage collector.
 *
 * Kotlin has no memory addresses, but upstream uses them: 'Arena::contains' and, with
 * 'opts.arenasort', the clauses are sorted by address ('pointer_rank' in collect.cpp). So the
 * arena keeps virtual addresses: every 'prepare' opens a new space with a fresh id, 'copy'
 * places the clause at the current 'top' offset (advanced by 'Clause::bytes'), and a clause
 * records its [Clause.space] and [Clause.address]. Clauses allocated with 'new' (outside the
 * arena) have space 0. Within one 'to' space the addresses grow in copy order, exactly as the
 * real pointers do, which is all 'pointer_rank' observes after 'copy_non_garbage_clauses'.
 *
 * 'char *copy (const char *p, size_t bytes)' -> [copy] (c): returns the new clause object
 * (the memcpy of the clause, see [Clause.memcpy]).
 */
internal class Arena {
    private var nextSpace = 0
    private var fromSpace = 0 // 0 = no space
    private var toSpace = 0
    private var toTop = 0L
    private var toEnd = 0L

    // Prepare 'to' space to hold that amount of memory.  Precondition is that
    // the 'to' space is empty.  The following sequence of 'copy' operations
    // can use as much memory in sum as pre-allocated here.
    fun prepare(bytes: Long) {
        check(toSpace == 0)
        toSpace = ++nextSpace
        toTop = 0
        toEnd = bytes
    }

    // Does the memory pointed to by 'p' belong to this arena? More precisely
    // to the 'from' space, since that is the only one remaining after 'swap'.
    fun contains(c: Clause): Boolean =
        c.space != 0 && (c.space == fromSpace || c.space == toSpace)

    // Allocate that amount of memory in 'to' space.  This assumes the 'to'
    // space has been prepared to hold enough memory with 'prepare'.  Then
    // copy the memory pointed to by 'p' of size 'bytes'.  Note that it does
    // not matter whether 'p' is in 'from' or allocated outside of the arena.
    fun copy(c: Clause): Clause {
        val bytes = c.bytes()
        val res = c.memcpy()
        res.space = toSpace
        res.address = toTop
        toTop += bytes
        check(toTop <= toEnd)
        return res
    }

    // Completely delete 'from' space and then replace 'from' by 'to' (by
    // pointer swapping).  Everything previously allocated (in 'from') and not
    // explicitly copied to 'to' with 'copy' becomes invalid.
    fun swap() {
        fromSpace = toSpace
        toSpace = 0
        toTop = 0
        toEnd = 0
    }
}

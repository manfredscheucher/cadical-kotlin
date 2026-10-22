package org.bytefred.ksat.cadical.full

/*
 * queue.hpp: links of the doubly linked VMTF decision queue and the queue anchors.
 *
 * Mapping: 'Links' (vector<Link>) -> 'ArrayList<Link>' (grown in 'enlarge' with fresh links,
 * which are zero like the value-initialized upstream elements). 'links[dst] = links[src]' in
 * 'compact' moves the reference (no aliasing there, see Compact.kt).
 */
internal class Link {
    var prev = 0 // variable indices
    var next = 0
    // initialized explicitly in 'init_queue'
}

internal typealias Links = ArrayList<Link>

// Variable move to front (VMTF) decision queue ordered by 'bumped'.  See
// our SAT'15 paper for an explanation on how this works.
internal class Queue {
    // We use integers instead of variable pointers.  This is more compact and
    // also avoids issues due to moving the variable table during 'resize'.
    var first = 0 // anchors (head/tail) for doubly linked list
    var last = 0
    var unassigned = 0 // all variables after this one are assigned
    var bumped = 0L // see 'Internal.update_queue_unassigned'

    // We explicitly provide the mapping of integer indices to links to the
    // following two (inlined) functions.  This avoids including
    // 'internal.hpp' and breaks a cyclic dependency, so we can keep their
    // code here in this header file.  Otherwise they are just ordinary doubly
    // linked list 'dequeue' and 'enqueue' operations.
    fun dequeue(links: Links, idx: Int) {
        val l = links[idx]
        if (l.prev != 0) links[l.prev].next = l.next else first = l.next
        if (l.next != 0) links[l.next].prev = l.prev else last = l.prev
    }

    fun enqueue(links: Links, idx: Int) {
        val l = links[idx]
        l.prev = last
        if (l.prev != 0) links[last].next = idx else first = idx
        last = idx
        l.next = 0
    }
}

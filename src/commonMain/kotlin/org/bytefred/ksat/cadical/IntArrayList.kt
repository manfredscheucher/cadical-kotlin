package org.bytefred.ksat.cadical

/** Minimal growable int list (avoids boxing), used by the full port in package `full`. */
class IntArrayList {
    private var a = IntArray(16)
    var size = 0
        private set
    fun add(x: Int) { if (size == a.size) a = a.copyOf(a.size * 2); a[size++] = x }
    operator fun get(i: Int): Int = a[i]
    operator fun set(i: Int, v: Int) { a[i] = v }
    fun removeLast() { size-- }
    fun removeAt(i: Int) { for (k in i until size - 1) a[k] = a[k + 1]; size-- }
    fun clear() { size = 0 }
    fun shrinkTo(n: Int) { size = n }
    fun toArray(): IntArray = a.copyOf(size)
    fun contains(x: Int): Boolean { for (k in 0 until size) if (a[k] == x) return true; return false }
}

/** Minimal growable boolean list, parallel to [IntArrayList] for the watcher 'bin' flag. */
class BooleanList {
    private var a = BooleanArray(16)
    var size = 0
        private set
    fun add(x: Boolean) { if (size == a.size) a = a.copyOf(a.size * 2); a[size++] = x }
    operator fun get(i: Int): Boolean = a[i]
    operator fun set(i: Int, v: Boolean) { a[i] = v }
    fun removeAt(i: Int) { for (k in i until size - 1) a[k] = a[k + 1]; size-- }
    fun clear() { size = 0 }
    fun shrinkTo(n: Int) { size = n }
}

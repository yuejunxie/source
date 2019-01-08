package java.util.concurrent;

import java.io.ObjectStreamField;
import java.io.Serializable;
import java.lang.reflect.ParameterizedType;
import java.lang.reflect.Type;
import java.util.AbstractMap;
import java.util.Map;

/**
 * Author: JackyShieh
 * Corporation: CornerStone LTD
 * WE LINK
 * source
 * Created: 2019/1/7 19:34
 * Description:
 */
public class ConcurrentHashMap<K, V> extends AbstractMap<K, V> implements ConcurrentMap<K, V>, Serializable {

//    常量
    /**
     * 最大容量 2^30
     */
    public static final int MAXIMUM_CAPACITY = 1 << 30;

    /**
     * 默认容量 2^4
     */
    public static final int DEFAULT_CAPACITY = 16;

    /**
     * 最大的toArraySize
     */
    static final int MAX_ARRAY_SIZE = Integer.MAX_VALUE - 8;
    /**
     *
     */
    private static final int DEFAULT_CONCURRENCY_LEVEL = 16;

    private static final float LOAD_FACTOR = 0.75f;

    static final int TREEIFY_THRESHOLD = 8;

    static final int UNTREEIFY_THRESHOLD = 6;

    static final int MIN_TREEIFY_CAPACITY = 64;
    //扩容线程所负责的区间大小最低为16，避免发生大量的内存冲突
    private static final int MIN_TRANSFER_STRIDE = 16;
    //用于生成当前数组对应的基数戳
    private static int RESIZE_STAMP_BITS = 16;
    //最多能有多少个线程能够帮助进行扩容，因为sizeCtl只有低16位用于标识，所以最多只有2^16-1个线程帮助扩容
    private static final int MAX_RESIZERS = (1 << (32 - RESIZE_STAMP_BITS)) - 1;

    //将基数戳左移的位数，保证左移后的基数戳为负值，然后再加上n+1,表示n个线程正在扩容
    private static final int RESIZE_STAMP_SHIFT = 32 - RESIZE_STAMP_BITS;

    // hash值为-1处的节点代表forwarding node
    static final int MOVED = -1; // hash for forwarding nodes
    //数组位置中红黑树根节点的hash值为-2，小于0
    static final int TREEBIN = -2; // hash for roots of trees
    static final int RESERVED = -3; // hash for transient reservations
    // 和key对应hash值进行与操作, 将hash值最高位置0
    static final int HASH_BITS = 0x7fffffff;

    static final int NCPU = Runtime.getRuntime().availableProcessors();

    private static final ObjectStreamField[] serialPersistentFields = {
            new ObjectStreamField("segments", Segment[].class),
            new ObjectStreamField("segmentMask", Integer.TYPE),
            new ObjectStreamField("segmentShift", Integer.TYPE)
    };

    //    Node
    static class Node<K, V> implements Map.Entry<K, V> {
        final int hash;
        final K key;
        volatile V val;
        volatile Node<K, V> next;

        Node(int hash, K key, V val, Node<K, V> next) {
            this.hash = hash;
            this.key = key;
            this.val = val;
            this.next = next;
        }

        public final K getKey() {
            return key;
        }

        public final V getValue() {
            return val;
        }

        public final int hashCode() {
            return key.hashCode() ^ val.hashCode();
        }

        public final String toString() {
            return key + "=" + val;
        }

        public final V setValue(V value) {
            throw new UnsupportedOperationException();
        }

        public final boolean equals(Object o) {
            Object k, v, u;
            Map.Entry<?, ?> e;
            return ((o instanceof Map.Entry) &&
                    (k = (e = (Map.Entry<?, ?>) o).getKey()) != null &&
                    (v = e.getValue()) != null &&
                    (k == key || k.equals(key)) &&
                    (v == (u = val) || v.equals(u)));
        }

        Node<K, V> find(int h, Object k) {
            Node<K, V> e = this;
            if (k != null) {
                do {
                    K ek;
                    if (e.hash == h &&
                            ((ek = e.key) == k || (ek != null && k.equals(ek))))
                        return e;
                } while ((e = e.next) != null);
            }
            return null;
        }
    }

//    静态工具方法

    static final int spread(int h) {
        return (h ^ (h >>> 16)) & HASH_BITS;
    }

    private static final int tableSizeFor(int c) {
        int n = c - 1;
        n |= n >>> 1;
        n |= n >>> 2;
        n |= n >>> 4;
        n |= n >>> 8;
        n |= n >>> 16;
        return (n < 0) ? 1 : (n >= MAXIMUM_CAPACITY) ? MAXIMUM_CAPACITY : n + 1;
    }

    static Class<?> comparableClassFor(Object x) {
        if (x instanceof Comparable) {
            Class<?> c;
            Type[] ts, as;
            Type t;
            ParameterizedType p;
            if ((c = x.getClass()) == String.class) // bypass checks
                return c;
            if ((ts = c.getGenericInterfaces()) != null) {
                for (int i = 0; i < ts.length; ++i) {
                    if (((t = ts[i]) instanceof ParameterizedType) &&
                            ((p = (ParameterizedType) t).getRawType() == Comparable.class) &&
                            (as = p.getActualTypeArguments()) != null &&
                            as.length == 1 && as[0] == c) // type arg is c
                        return c;
                }
            }
        }
        return null;
    }

    static int compareComparables(Class<?> kc, Object k, Object x) {
        return (x == null || x.getClass() != kc ? 0 :
                ((Comparable) k).compareTo(x));
    }

    static final <K, V> Node<K, V> tabAt(Node<K, V>[] tab, int i) {
        return (Node<K, V>) U.getObjectVolatile(tab, ((long) i << ASHIFT) + ABASE);
    }

    static final <K, V> boolean casTabAt(Node<K, V>[] tab, int i, Node<K, V> c, Node<K, V> v) {
        return U.compareAndSwapObject(tab, ((long) i << ASHIFT) + ABASE, c, v);
    }

    static final <K, V> void setTabAt(Node<K, V>[] tab, int i, Node<K, V> v) {
        U.putObjectVolatile(tab, ((long) i << ASHIFT) + ABASE, v);
    }

    //    字段

    //节点数组，用于存储键值对，当第一次插入时进行初始化。
    transient volatile Node<K, V>[] table;

    //只有当数组处于扩容过程时，nextTable才不为null;否则其他时刻，nextTable为null;
    //nextTable主要用于扩容过程中指向扩容后的新数组
    private transient volatile Node<K, V>[] nextTable;

    private transient volatile long baseCount;

    private transient volatile int sizeCtl;

    //用于扩容过程中，指示原数组下一个分割区间的上界位置
    private transient volatile int transferIndex;

    private transient volatile int cellsBusy;

    private transient volatile CounterCell[] counterCells;

    // views

    private transient KeySetView<K, V> keySet;
    private transient ValuesView<K, V> values;
    private transient EntrySetView<K, V> entrySet;

//    公共方法

    public ConcurrentHashMap() {
    }

    public ConcurrentHashMap(int initialCapacity) {
        if (initialCapacity < 0)
            throw new IllegalArgumentException();
        int cap = ((initialCapacity >= (MAXIMUM_CAPACITY >>> 1)) ?
                MAXIMUM_CAPACITY :
                tableSizeFor(initialCapacity + (initialCapacity >>> 1) + 1));
        this.sizeCtl = cap;
    }

    public ConcurrentHashMap(Map<? extends K, ? extends V> m) {
        this.sizeCtl = DEFAULT_CAPACITY;
        putAll(m);
    }

    public ConcurrentHashMap(int initialCapacity, float loadFactor) {
        this(initialCapacity, loadFactor, 1);
    }

    public ConcurrentHashMap(int initialCapacity, float loadFactor, int concurrencyLevel) {
        if (!(loadFactor > 0.0f) || initialCapacity < 0 || concurrencyLevel <= 0)
            throw new IllegalArgumentException();
        if (initialCapacity < concurrencyLevel)   // Use at least as many bins
            initialCapacity = concurrencyLevel;   // as estimated threads
        long size = (long) (1.0 + (long) initialCapacity / loadFactor);
        int cap = (size >= (long) MAXIMUM_CAPACITY) ?
                MAXIMUM_CAPACITY : tableSizeFor((int) size);
        this.sizeCtl = cap;
    }

    @Override
    public int size() {
        long n = sumCount();
        return ((n < 0L) ? 0 : (n > (long) Integer.MAX_VALUE) ? Integer.MAX_VALUE : (int) n);
    }

    public boolean isEmpty() {
        return sumCount() <= 0L; // ignore transient negative values
    }

    @Override
    public V get(Object key) {
        Node<K, V>[] tab;
        Node<K, V> e, p;
        int n, eh;
        K ek;
        int h = spread(key.hashCode());
        if ((tab = table) != null && (n = tab.length) > 0 && (e = tabAt(tab, (n - 1) & h) != null)) {
//            第一个匹配
            if ((eh = e.hash) == h) {
                if ((ek = e.key) == key || (ek != null && key.equals(ek))) {
                    return e.val;
                }
            } else if (eh < 0) {
                //树
                return (p = e.find(h, key)) != null ? p.val : null;
            }
            // 链表
            while ((e = e.next) != null)
                if (e.hash == h && ((ek = e.key) == key || (ek != null && key.equals(ek))))
                    return e.val;
        }
        return null;
    }

    @Override
    public boolean containsKey(Object key) {
        return get(key) != null;
    }

    @Override
    public boolean containsValue(Object value) {
        if (value == null)
            throw new NullPointerException();
        Node<K, V>[] t;
        if ((t = table) != null) {
            Traverser<K, V> it = new Traverser<K, V>(t, t.length, 0, t.length);
            for (Node<K, V> p; (p = it.advance()) != null; ) {
                V v;
                if ((v = p.val) == value || (v != null && value.equals(v))) {
                    return true;
                }
            }
        }
        return false;
    }

    @Override
    public V put(K key, V value) {
        return putVal(key, value, false);
    }

    final V putVal(K key, V value, boolean onlyIfAbsent) {
        if (key == null || value == null) throw new NullPointerException();
        int hash = spread(key.hashCode());
        int binCount = 0;
        //死循环直至插入成功
        for (Node<K, V>[] tab = table; ; ) {
            Node<K, V> f;
            int n, i, fh;
            if (tab == null || (n = tab.length) == 0)
                //初始化table
                tab = initTable();
            else if ((f = tabAt(tab, i = (n - 1) & hash)) == null) {
                //如果hash值对应位置处为null, 直接添加即可
                ////无需加锁, 进行CAS操作, 在i位置处添加新hash对应的键值对

            } else if ((fh = f.hash) == MOVED) {
                //f.hash==-1说明其他线程正在进行扩容操作
                //调用helpTransfer函数进行扩容操作
                tab = helpTransfer(tab, f);
            } else {
                V oldVal = null;
                synchronized (f) {
                    //双重检查机制
                    //重复检查，避免多线程导致的修改
                    if (tabAt(tab, i) == f) {
                        if (fh > 0) {
                            //链表
                            binCount = 1;
                            for (Node<K, V> e = f; ; ++binCount) {
                                K ek;
                                //替换
                                if (e.hash == hash && ((ek = e.key) == key || (ek != null && key.equals(ek)))) {
                                    oldVal = e.val;
                                    if (!onlyIfAbsent) e.val = value;
                                    break;
                                }
                                //新增
                                Node<K, V> pred = e;
                                if ((e = e.next) == null) {
                                    pred.next = new Node<>(hash, key, value, null);
                                    break;
                                }
                            }
                        } else if (f instanceof TreeBin) {
                            //红黑树
                            Node<K, V> p;
                            binCount = 2;
                            if ((p = ((TreeBin<K, V>) f).putTreeVal(hash, key, value)) != null) {
                                oldVal = p.val;
                                if (!onlyIfAbsent)
                                    p.val = value;
                            }

                        }
                        //死循环
                    }
                }
                if (binCount != 0) {
                    if (binCount >= TREEIFY_THRESHOLD)
//                        树化节点
                        treefyBin(tab, i);
                    if (oldVal != null)
//                        修改值不需要addCount
                        return oldVal;
//                    新增加KV，跳到addCount
                    break;
                }
            }
        }
        //调用addCount函数，将容器大小加1，并判断是否需要进行扩容
        addCount(1L, binCount);
        return null;
    }

    @Override
    public void putAll(Map<? extends K, ? extends V> m) {
        tryPresize(m.size());
        for (Map.Entry<? extends K, ? extends V> e : m.entrySet())
            putVal(e.getKey(), e.getValue(), false);
    }

    /* ---------------- Table Initialization and Resizing -------------- */
    static final int resizeStamp(int n) {
        return Integer.numberOfLeadingZeros(n) | (1 << (RESIZE_STAMP_BITS - 1));
    }

    private final Node<K, V>[] initTable() {
        Node<K, V>[] tab;
        int sc;
        //死循环直至初始化成功
        while ((tab = table) == null || tab.length == 0) {
            //如果当前有线程在对table进行初始化,则当前线程被阻塞,这也可以看出ConcurrentHashMap的初始化只能由一个线程完成
            if ((sc = sizeCtl) < 0)
                //如果sizeCtl<0, 这代表有其他线程正在初始化或者扩容
                //暂停初始化步骤, 让出处理器, 进行旋转
                Thread.yield();
            else if (U.compareAndSwapInt(this, SIZECTL, sc, -1)) {
                //利用CAS方法把sizectl的值置为-1,防止其他线程进入,表示本线程正在进行初始化
                try {
                    //双重检查机制
                    if ((tab = table) == null || tab.length == 0) {
                        int n = sc > 0 ? sc : DEFAULT_CAPACITY;
                        Node<K, V>[] nt = (Node<K, V>[]) new Node<?, ?>[n];
                        table = tab = nt;
                        //相当于0.75*n 设置一个扩容的阈值
                        //LOADFACTOR*CAPACITY
                        sc = n - (n >>> 2);
                    }
                } finally {
                    // 作为下一次扩容的临界值
                    sizeCtl = sc;
                }
                break;
            }
        }
        return tab;
    }

    private final void addCount(long x, int check) {
        CounterCell[] as;
        long b, s;
        // 尝试使用CAS更新baseCount失败
        if ((as = counterCells) != null || !U.compareAndSwapLong(this, BASECOUNT, b = baseCount, s = b + x)) {
            // 转用CounterCells进行更新
            CounterCell a;
            long v;
            int m;
            boolean uncontended = true;
            // 在CounterCells未初始化
            // 或尝试通过CAS更新当前线程的CounterCell失败时
            if (as == null || (m = as.length - 1) < 0 ||
                    (a = as[ThreadLocalRandom.getProbe() & m]) == null
                    || !(uncontended = U.compareAndSwapLong(a, CELLVALUE, v = a.value, v + x))) {
                // 多线程修改baseCount时，竞争失败的线程会执行fullAddCount(x, uncontended),把x的值插入到counterCell类中
                // 调用fullAddCount()，该函数负责初始化CounterCells和更新计数
                fullAddCount(x, uncontended);
            }
            if (check <= 1) {
                return;
            }
            // 统计总数
            s = sumCount();
        }
        //counterCells是一个元素为CounterCell的数组，该数组的大小与当前机器的CPU数量有关，并且它不会被主动初始化，只有在调用fullAddCount()函数时才会进行初始化。
        if (check > 0) {
            // 判断是否需要扩容，在上文中已经讲过了
            Node<K, V>[] tab, nt;
            int n, sc;
            while (s > (long) (sc = sizeCtl) && (tab = table) != null
                    && (n = tab.length) < MAXIMUM_CAPACITY) {
                int rs = resizeStamp(n);
                if (sc < 0) {
                    if ((sc >>> RESIZE_STAMP_SHIFT) != rs || sc == rs + 1 ||
                            sc == rs + MAX_RESIZERS || (nt = nextTable) == null ||
                            transferIndex <= 0) {
                        // 其他线程在初始化，break；
                        break;
                    }
                    if (U.compareAndSwapInt(this, SIZECTL, sc, sc + 1))
                        // 其他线程正在扩容，协助扩容
                        transfer(tab, nt);
                } else if (U.compareAndSwapInt(this, SIZECTL, sc, (rs << RESIZE_STAMP_SHIFT) + 2))
                    // 仅当前线程在扩容
                    transfer(tab, null);
                s = sumCount();
            }
        }
    }

    //helpTransfer函数的主要作用是如果有线程正在进行扩容操作,则帮助其他线程进行扩容操作
    final Node<K, V>[] helpTransfer(Node<K, V>[] tab, Node<K, V> f) {
        Node<K, V>[] nextTab;
        int sc;
        //如果tab不为null,且f为转移节点,且新table不为null
        if (tab != null && (f instanceof ForwardingNode) &&
                (nextTab = ((ForwardingNode<K, V>) f).nextTable) != null) {
            //返回resize后的table的标记位
            int rs = resizeStamp(tab.length);
            while (nextTab == nextTable && table == tab && (sc = sizeCtl) < 0) {
                if ((sc >>> RESIZE_STAMP_SHIFT) != rs || sc == rs + 1 || sc == rs + MAX_RESIZERS || transferIndex <= 0) {
                    break;
                    //CAS修改sizeCtl=sizeCtl+1,表示新增加一个线程辅助扩容
                    if (U.compareAndSwapInt(this, SIZECTL, sc, sc + 1)) {
                        transfer(tab, nextTab);
                        break;
                    }
                }
            }
            return nextTab;
        }
        return table;
    }

    private final void transfer(Node<K, V>[] tab, Node<K, V>[] nextTab) {
        int n = tab.length, stride;
        // 每个线程所负责转移的数组的区间最少为MIN_TRANSFER_STRIDE=16,
        // 也就是说数组的连续16个位置都是由这个线程来进行转移，
        // 其他线程不允许接触这连续的16个位置，必须发生线程之间大量的内存冲突。
        // 换另一个角度来说，每个线程负责连续16个大小区间的数组转移。
        if ((stride = (NCPU > 1) ? (n >>> 3) / NCPU : n) < MIN_TRANSFER_STRIDE)
            stride = MIN_TRANSFER_STRIDE;
        // 初始化生成新的扩容数组
        if (nextTab == null) {
            try {
                Node<K, V>[] nt = (Node<K, V>[]) new Node<?, ?>[n << 1];
                nextTab = nt;
            } catch (Throwable ex) {
                sizeCtl = Integer.MAX_VALUE;
                return;
            }
            //nextTable为类成员变量，只有在扩容的过程中有作用，在其他时刻都是null值。nextTable指向新数组
            nextTable = nextTab;
            //转移后的节点偏移量
            transferIndex = n;
        }
        int nextn = nextTab.length;
        ForwardingNode<K, V> fwd = new ForwardingNode<K, V>(nextTab);
        boolean advance = true;//遍历
        boolean finishing = false;
        //保证在提交扩容后的新数组时，原数组中的所有元素都已经被遍历
        for (int i = 0, bound = 0; ; ) {
            Node<K, V> f;
            int fh;
            while (advance) {
                int nextIndex, nextBound;
                if (--i >= bound || finishing) {
                    //bound为数组区间下限值，i为当前转移数组的位置,--i处理转移下一个节点位置，从后往前处理
                    advance = false;//退出while循环
                } else if ((nextIndex = transferIndex) <= 0) {
                    //表示原数组已经分割完了
                    i = -1;
                    advance = false;//退出while循环
                }
                //CAS操作修改transferIndex值，代表下一个线程转移原数组的节点的位置
                else if (U.compareAndSwapInt(this, TRANSFERINDEX, nextIndex, nextBound = (nextIndex > stride ? nextIndex - stride : 0))) {
                    bound = nextBound;//设置当前线程转移原数组区间的下限值
                    i = nextIndex - 1;  //从后往前处理
                    advance = false;//退出while循环
                }
            }
            if (i < 0 || i > n || i + n > nextn) {
                int sc;
                if (finishing) { //扩容完成
                    nextTable = null;  //将nextTable置为null，表示当前扩容过程完成
                    table = nextTab; //table指向扩容后的新数组
                    sizeCtl = (n << 1) - (n >>> 1); //将sizeCtl设置为正数，设置为原数组的3/2，即新数组的3/4
                    return;
                }
                if (U.compareAndSwapInt(this, SIZECTL, sc = sizeCtl, sc - 1)) {
                    if ((sc - 2) != resizeStamp(n) << RESIZE_STAMP_SHIFT)
                        //因为只有一个线程扩容时sc=resizeStamp(n)+2,所以该if语句是在最后一个线程完成扩容操作时，将finishing置为true，表示正确完成。
                        return;
                    finishing = advance = true;
                    i = n;
                }
            }
            //将原数组相应位置直接设置为fwd,表示该位置已经遍历过
            else if ((f = tabAt(tab, i)) == null) {
                advance = casTabAt(tab, i, null, fwd);
            }
            // 表示该数组位置已经被其他线程处理过了
            else if ((fh = f.hash) == MOVED) {
                advance = true;
            }
            //否则需要将原数组位置相应元素复制到新数组上
            else {
                synchronized (f) {
                    if (tabAt(tab, i) == f) {
                        //再次核对，防止其他线程对该hash值进行修改
                        Node<K, V> ln, hn;
                        if (fh >= 0) {
                            //说明该位置存放的是普通节点
                            int runBit = fh & n;//判断原数组中的节点的hash的 log(n)位为0或者1
                            Node<K, V> lastRun = f;
                            for (Node<K, V> p = f.next; p != null; p = p.next) {
                                int b = p.hash & n;
                                if (b != runBit) {
                                    runBit = b;
                                    lastRun = p;
                                }
                            }
                            if (runBit == 0) {
                                //指向链表的最后出现连续log(n)位为0的第一个节点
                                ln = lastRun;
                                hn = null;
                            } else {
                                //指向链表的最后出现连续log(n)位为1的第一个节点
                                hn = lastRun;
                                ln = null;
                            }
                            for (Node<K, V> p = f; p != lastRun; p = p.next) {
                                int ph = p.hash;
                                K pk = p.key;
                                V pv = p.val;
                                if ((ph & n) == 0)
                                    ln = new Node<K, V>(ph, pk, pv, ln);
                                else
                                    hn = new Node<K, V>(ph, pk, pv, hn);
                            }
                            //将hash值的 log(n) 位为0的节点链表复制到新数组对应原来数组的位置
                            setTabAt(nextTab, i, ln);
                            //将Hash值的 log(n) 位为1的节点链表复制到新数组对应原来数组位置+n
                            setTabAt(nextTab, i + n, hn);
                            //将该数组位置设置为已处理
                            setTabAt(tab, i, fwd);
                            advance = true;
                        }
                        //说明该数组位置是红黑树根节点
                        else if (f instanceof TreeBin) {
                            TreeBin<K, V> t = (TreeBin<K, V>) f;
                            TreeNode<K, V> lo = null, loTail = null;
                            TreeNode<K, V> hi = null, hiTail = null;
                            int lc = 0, hc = 0;
                            for (Node<K, V> e = t.first; e != null; e = e.next) {
                                int h = e.hash;
                                TreeNode<K, V> p = new TreeNode<K, V>
                                        (h, e.key, e.val, null, null);
                                if ((h & n) == 0) {
                                    //判断红黑树中节点的hash值的 log(n) 位为0，说明该节点应该存放到新数组中对应原数组的位置
                                    if ((p.prev = loTail) == null)
                                        lo = p;
                                    else
                                        loTail.next = p;
                                    loTail = p;
                                    ++lc;
                                }
                                //判断红黑树中节点的hash值的 log(n) 位为1，说明该节点应该存放到新数组中对应原数组位置+n
                                else {
                                    if ((p.prev = hiTail) == null)
                                        hi = p;
                                    else
                                        hiTail.next = p;
                                    hiTail = p;
                                    ++hc;
                                }
                            }
                            //根据链表中节点的个数和UNTREEIFY_THRESHOLD进行比较，如果小于等于，则不需要将链表转换为红黑树；如果大于，则需要将链表转换为红黑树
                            ln = (lc <= UNTREEIFY_THRESHOLD) ? untreeify(lo) :
                                    (hc != 0) ? new TreeBin<K, V>(lo) : t;
                            hn = (hc <= UNTREEIFY_THRESHOLD) ? untreeify(hi) :
                                    (lc != 0) ? new TreeBin<K, V>(hi) : t;
                            setTabAt(nextTab, i, ln);//复制到新数组中
                            setTabAt(nextTab, i + n, hn);//复制到新数组中
                            setTabAt(tab, i, fwd);//将原数组中相应位置为fwd，表示该位置已经被处理过
                            advance = true;//继续进行遍历
                        }
                    }
                }
            }
        }
    }

    //将原数组进行两倍扩容
    private final void tryPresize(int size) {
        int c = (size >= (MAXIMUM_CAPACITY >>> 1)) ? MAXIMUM_CAPACITY :
                tableSizeFor(size + (size >>> 1) + 1);
        int sc;
        while ((sc = sizeCtl) >= 0) {   //说明数组不是处于扩容状态
            Node<K, V>[] tab = table;
            int n;
            if (tab == null || (n = tab.length) == 0) {   //如果数组为null
                n = (sc > c) ? sc : c;
                if (U.compareAndSwapInt(this, SIZECTL, sc, -1)) {   //将sc设置为-1，表示当前数组正在进行扩容操作
                    try {
                        if (table == tab) {
                            @SuppressWarnings("unchecked")
                            Node<K, V>[] nt = (Node<K, V>[]) new Node<?, ?>[n];   //生成新的数组
                            table = nt;  //table指向新数组
                            sc = n - (n >>> 2);  //sc保存新数组的上限值
                        }
                    } finally {
                        sizeCtl = sc;
                    }
                }
            } else if (c <= sc || n >= MAXIMUM_CAPACITY)
                break;
            else if (tab == table) {
                int rs = resizeStamp(n);
                if (sc < 0) {
                    Node<K, V>[] nt;
                    if ((sc >>> RESIZE_STAMP_SHIFT) != rs || sc == rs + 1 ||
                            sc == rs + MAX_RESIZERS || (nt = nextTable) == null ||
                            transferIndex <= 0)
                        break;
                    if (U.compareAndSwapInt(this, SIZECTL, sc, sc + 1))  //辅助扩容操作，将sizeCtl加1，表示新增加一个线程辅助扩容
                        transfer(tab, nt);
                } else if (U.compareAndSwapInt(this, SIZECTL, sc,
                        (rs << RESIZE_STAMP_SHIFT) + 2))   //开始进行扩容，通过CAS操作将sizeCtl置为负值，代表只要一个线程在进行扩容操作。
                    transfer(tab, null);
            }
        }
    }

    /* ---------------- Counter support -------------- */

    @sun.misc.Contended
    static final class CounterCell {
        volatile long value;

        CounterCell(long x) {
            value = x;
        }
    }

    final long sumCount() {
        CounterCell[] as = counterCells;
        CounterCell a;
        long sum = baseCount;
        if (as != null) {
            for (int i = 0; i < as.length; ++i) {
                if ((a = as[i]) != null)
                    sum += a.value;
            }
        }
        return sum;
    }

    private final void fullAddCount(long x, boolean wasUncontended) {
        int h;
        // 当前线程的probe等于0，证明该线程的ThreadLocalRandom还未被初始化
        // 以及当前线程是第一次进入该函数
        if ((h = ThreadLocalRandom.getProbe()) == 0) {
            // 初始化ThreadLocalRandom，当前线程会被设置一个probe
            ThreadLocalRandom.localInit();
            // probe用于在CounterCell数组中寻址
            h = ThreadLocalRandom.getProbe();
            // 未竞争标志
            wasUncontended = true;
        }
        //冲突标志
        boolean collide = false;
        for (; ; ) {
            CounterCell[] as;
            CounterCell a;
            int n;
            long v;
            // CounterCell数组已初始化
            if ((as = counterCells) != null && (n = as.length) > 0) {
                // 如果寻址到的Cell为空，那么创建一个新的Cell
                if ((a = as[(n - 1) & h]) == null) {
                    // cellsBusy是一个只有0和1两个状态的volatile整数
                    // 它被当做一个自旋锁，0代表无锁，1代表加锁
                    if (cellsBusy == 0) {
                        // 将传入的x作为初始值创建一个新的CounterCell
                        CounterCell r = new CounterCell(x);
                        // 通过CAS尝试对自旋锁加锁
                        if (cellsBusy == 0 && U.compareAndSwapInt(this, CELLSBUSY, 0, 1)) {
                            // 加锁成功，声明Cell是否创建成功的标志
                            boolean created = false;
                            try {
                                CounterCell[] rs;
                                int m, j;
                                // 再次检查CounterCell数组是否不为空
                                // 并且寻址到的Cell为空
                                if ((rs = counterCells) != null &&
                                        (m = rs.length) > 0 &&
                                        rs[j = (m - 1) & h] == null) {
                                    // 将之前创建的新Cell放入数组
                                    rs[j] = r;
                                    created = true;
                                }
                            } finally {
                                // 释放锁
                                cellsBusy = 0;
                            }
                            if (created)
                                break;
                            // 如果未成功
                            // 代表as[(n - 1) & h]这个位置的Cell已经被其他线程设置
                            // 那么就从循环头重新开始
                            continue;
                        }
                    }
                    collide = false;
                }
                // as[(n - 1) & h]非空
                // 在addCount()函数中通过CAS更新当前线程的Cell进行计数失败
                // 会传入wasUncontended = false，代表已经有其他线程进行竞争
                else if (!wasUncontended) {
                    // 设置未竞争标志，之后会重新计算probe，然后重新执行循环
                    wasUncontended = true;

                }
                // 尝试进行计数，如果成功，那么就退出循环
                else if (U.compareAndSwapLong(a, CELLVALUE, v = a.value, v + x))
                    break;
                else if (counterCells != as || n > NCPU) {
                    // 尝试更新失败，检查counterCell数组是否已经扩容
                    // 或者容量达到最大值（CPU的数量）
                    // 设置冲突标志，防止跳入下面的扩容分支
                    // 之后会重新计算probe
                    collide = false;
                } else if (!collide) {
                    // 设置冲突标志，重新执行循环
                    // 如果下次循环执行到该分支，并且冲突标志仍然为true
                    // 那么会跳过该分支，到下一个分支进行扩容
                    collide = true;
                }
                // 尝试加锁，然后对counterCells数组进行扩容
                else if (cellsBusy == 0 && U.compareAndSwapInt(this, CELLSBUSY, 0, 1)) {
                    try {
                        // 检查是否已被扩容
                        if (counterCells == as) {
                            // 新数组容量为之前的1倍
                            CounterCell[] rs = new CounterCell[n << 1];
                            // 迁移数据到新数组
                            for (int i = 0; i < n; ++i)
                                rs[i] = as[i];
                            counterCells = rs;
                        }
                    } finally {
                        // 释放锁
                        cellsBusy = 0;
                    }
                    collide = false;
                    // 重新执行循环
                    continue;
                }
                // 为当前线程重新计算probe
                h = ThreadLocalRandom.advanceProbe(h);
            }
            // 通过CAS尝试对自旋锁加锁
            // CounterCell数组未初始化，尝试获取自旋锁，然后进行初始化
            else if (cellsBusy == 0 && counterCells == as &&
                    U.compareAndSwapInt(this, CELLSBUSY, 0, 1)) {
                boolean init = false;
                try {
                    if (counterCells == as) {
                        // 初始化CounterCell数组，初始容量为2
                        CounterCell[] rs = new CounterCell[2];
                        // 初始化CounterCell
                        rs[h & 1] = new CounterCell(x);
                        counterCells = rs;
                        init = true;
                    }
                } finally {
                    // 释放锁
                    cellsBusy = 0;
                }
                // 初始化CounterCell数组成功，退出循环
                if (init)
                    break;
            }
            // 如果自旋锁被占用，则只好尝试更新baseCount
            else if (U.compareAndSwapLong(this, BASECOUNT, v = baseCount, v + x)) {
                break;
            }
        }
    }

    /* ----------------Table Traversal -------------- */

    static final class TableStack<K, V> {
        int length;
        int index;
        Node<K, V>[] tab;
        TableStack<K, V> next;
    }

    static class Traverser<K, V> {
        Node<K, V>[] tab;
        Node<K, V> next;
        TableStack<K, V> stack, spare;
        int index;
        int baseIndex;
        int baseLimit;
        final int baseSize;

        public Traverser(Node<K, V>[] tab, int size, int index, int limit) {
            this.tab = tab;
            this.baseIndex = this.index = index;
            this.baseLimit = limit;
            this.baseSize = size;
            this.next = null;
        }

        final Node<K, V> advance() {
            Node<K, V> e;
            if ((e = next) != null)
                e = e.next;
            for (; ; ) {
                Node<K, V>[] t;
                int i, n;
                if (e != null)
                    return next = e;
                if (baseIndex > baseLimit || (t = tab) == null
                        || (n = t.length) <= (i = index) || i < 0) {
                    return next = null;
                }
                if ((e = tabAt(t, i)) != null && e.hash < 0) {
                    if (e instanceof ForwardingNode) {
                        tab = ((ForwardingNode<K, V>) e).nextTable;
                        e = null;
                        pushState(t, i, n);
                        continue;
                    } else if (e instanceof TreeBin) {
                        e = ((TreeBin<K, V>) e).first();
                    } else e = null;
                }
                if (stack != null)
                    recoverState(n);
                else if ((index = i + baseSize) >= n)
                    index = ++baseIndex;
            }
        }

        private void pushState(Node<K, V>[] t, int i, int n) {
            TableStack<K, V> s = spare;  // reuse if possible
            if (s != null)
                spare = s.next;
            else
                s = new TableStack<K, V>();
            s.tab = t;
            s.length = n;
            s.index = i;
            s.next = stack;
            stack = s;
        }

        private void recoverState(int n) {
            TableStack<K, V> s;
            int len;
            while ((s = stack) != null && (index += (len = s.length)) >= n) {
                n = len;
                index = s.index;
                tab = s.tab;
                s.tab = null;
                TableStack<K, V> next = s.next;
                s.next = spare; // save for reuse
                stack = next;
                spare = s;
            }
            if (s == null && (index += baseSize) >= n)
                index = ++baseIndex;
        }


    }

    // Unsafe mechanics
    private static final sun.misc.Unsafe U;
    private static final long SIZECTL;
    private static final long TRANSFERINDEX;
    private static final long BASECOUNT;
    private static final long CELLSBUSY;
    private static final long CELLVALUE;
    private static final long ABASE;
    private static final int ASHIFT;

    static {
        try {
            U = sun.misc.Unsafe.getUnsafe();
            Class<?> k = ConcurrentHashMap.class;
            SIZECTL = U.objectFieldOffset
                    (k.getDeclaredField("sizeCtl"));
            TRANSFERINDEX = U.objectFieldOffset
                    (k.getDeclaredField("transferIndex"));
            BASECOUNT = U.objectFieldOffset
                    (k.getDeclaredField("baseCount"));
            CELLSBUSY = U.objectFieldOffset
                    (k.getDeclaredField("cellsBusy"));
            Class<?> ck = CounterCell.class;
            CELLVALUE = U.objectFieldOffset
                    (ck.getDeclaredField("value"));
            Class<?> ak = Node[].class;
            ABASE = U.arrayBaseOffset(ak);
            int scale = U.arrayIndexScale(ak);
            if ((scale & (scale - 1)) != 0)
                throw new Error("data type scale not a power of two");
            ASHIFT = 31 - Integer.numberOfLeadingZeros(scale);
        } catch (Exception e) {
            throw new Error(e);
        }
    }
}

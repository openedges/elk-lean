// Differential harness for elk-lean's `Elk.Core.Util.JavaHashSet` (java.util.HashSet / HashMap bins,
// resize splits, tree bins). Replays an operation file on a java.util.HashSet<K> (K: a chosen hashCode,
// equality by id) and prints the iteration order at every "p" line; stderr gets the largest number of
// tree bins seen and the number of operations after which a tree bin existed.
//
//   javac -d <dir> scripts/java/HashSetOrder.java
//   python3 scripts/gen_hashset_ops.py tests/fixtures/spv/hashset_ops.txt 1 1500
//   java --add-opens java.base/java.util=ALL-UNNAMED -cp <dir> HashSetOrder tests/fixtures/spv/hashset_ops.txt \
//     > tests/fixtures/spv/hashset_ops.java.txt
//
// Operations: "a id h" add, "r id h" remove, "i id h" iterator removal, "R id h id h ..." removeAll of a
// list, "c" clear, "p" print. The Lean suite spv.javaHashSet (tests/lean/Tests/Api/RandomJavaSpv.lean)
// replays the same file and compares every printed order.
import java.io.BufferedReader;
import java.io.FileReader;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;

public final class HashSetOrder {
    static final class K {
        final int id;
        final int h;
        K(int id, int h) { this.id = id; this.h = h; }
        @Override public int hashCode() { return h; }
        @Override public boolean equals(Object o) { return o instanceof K && ((K) o).id == id; }
    }

    public static void main(String[] args) throws Exception {
        java.lang.reflect.Field mf = HashSet.class.getDeclaredField("map"); mf.setAccessible(true);
        java.lang.reflect.Field tf = java.util.HashMap.class.getDeclaredField("table"); tf.setAccessible(true);
        int maxTrees = 0, treeOps = 0;
        HashSet<K> set = new HashSet<>();
        StringBuilder out = new StringBuilder();
        try (BufferedReader r = new BufferedReader(new FileReader(args[0]))) {
            String line;
            while ((line = r.readLine()) != null) {
                String[] p = line.trim().split(" ");
                switch (p[0]) {
                case "a": set.add(new K(Integer.parseInt(p[1]), (int) Long.parseLong(p[2]))); break;
                case "r": set.remove(new K(Integer.parseInt(p[1]), (int) Long.parseLong(p[2]))); break;
                case "i": {
                    int id = Integer.parseInt(p[1]);
                    for (Iterator<K> it = set.iterator(); it.hasNext();) {
                        if (it.next().id == id) { it.remove(); }
                    }
                    break;
                }
                case "R": {
                    List<K> c = new ArrayList<>();
                    for (int i = 1; i + 1 < p.length; i += 2) {
                        c.add(new K(Integer.parseInt(p[i]), (int) Long.parseLong(p[i + 1])));
                    }
                    set.removeAll(c);
                    break;
                }
                case "c": set.clear(); break;
                case "p": {
                    StringBuilder b = new StringBuilder();
                    for (K k : set) { b.append(k.id).append(' '); }
                    out.append(b.toString().trim()).append('\n');
                    break;
                }
                default: break;
                }
                Object[] tab = (Object[]) tf.get(mf.get(set));
                int trees = 0;
                if (tab != null) for (Object o : tab) if (o != null && o.getClass().getName().endsWith("TreeNode")) trees++;
                maxTrees = Math.max(maxTrees, trees);
                if (trees > 0) treeOps++;
            }
        }
        System.out.print(out);
        System.err.println("maxTrees=" + maxTrees + " opsWithTrees=" + treeOps);
    }
}

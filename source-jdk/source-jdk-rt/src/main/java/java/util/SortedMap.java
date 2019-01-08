package java.util;

/**
 * Author: JackyShieh
 * Corporation: CornerStone LTD
 * WE LINK
 * source
 * Created: 2019/1/5 15:46
 * Description:
 */
public interface SortedMap<K, V> extends Map<K, V> {

    Comparator<? super K> comparator();

    SortedMap<K, V> subMap(K fromKey, K toKey);

    SortedMap<K, V> headMap(K toKey);

    SortedMap<K, V> tailMap(K fromKey);

    K firstKey();

    K lastKey();

    @Override
    Set<K> keySet();

    @Override
    Collection<V> values();

    @Override
    Set<Map.Entry<K, V>> entrySet();
}

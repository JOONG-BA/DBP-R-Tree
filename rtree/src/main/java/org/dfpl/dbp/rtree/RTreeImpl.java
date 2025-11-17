package org.dfpl.dbp.rtree;

import java.util.Iterator;
import java.util.List;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedList;
import java.util.PriorityQueue;

import java.awt.Color;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.RenderingHints;
import javax.swing.JFrame;
import javax.swing.JPanel;
import javax.swing.SwingUtilities;
import javax.swing.JOptionPane;

// RTreeImpl 클래스. RTree 인터페이스를 구현하고 GUI 및 모든 로직을 포함.
public class RTreeImpl implements RTree {

    private static final int MAX_ENTRIES = 4;
    private static final int MIN_ENTRIES = 2;

    private Node root;
    private int size;

    private JFrame guiFrame;
    private RTreePanel guiPanel;
    private volatile Rectangle currentSearchRect;
    private volatile Point currentKnnSource;
    private volatile List<Point> highlightedPoints = Collections.synchronizedList(new ArrayList<>());
    private boolean firstDeleteCall = true;

    // Node 내부 클래스. 트리의 노드(가지 또는 나뭇잎)를 정의.
    class Node {
        Rectangle mbr;
        boolean leaf;
        List<Node> children;
        List<Point> points;
        Node parent;

        public Node(boolean leaf, Node parent) {
            this.leaf = leaf;
            this.parent = parent;
            this.mbr = createInvalidMbr();
            if (leaf) {
                this.points = new ArrayList<>(MAX_ENTRIES + 1);
                this.children = null;
            } else {
                this.children = new ArrayList<>(MAX_ENTRIES + 1);
                this.points = null;
            }
        }

        public Rectangle getMbr() {
            if (!hasValidMbr()) {
                return createInvalidMbr();
            }
            return this.mbr;
        }

        public Rectangle getEntryMbr(Object entry) {
            if (entry instanceof Point) {
                Point p = (Point) entry;
                return new Rectangle(p, p);
            } else if (entry instanceof Node) {
                return ((Node) entry).getMbr();
            }
            return createInvalidMbr();
        }

        public boolean hasValidMbr() {
            return mbr.getLeftTop().getX() != Double.POSITIVE_INFINITY;
        }

        public void recalcMbr() {
            if (leaf) {
                if (points.isEmpty()) {
                    this.mbr = createInvalidMbr();
                    return;
                }
                Point p = points.get(0);
                double minX = p.getX(), minY = p.getY(), maxX = p.getX(), maxY = p.getY();
                for (int i = 1; i < points.size(); i++) {
                    p = points.get(i);
                    minX = Math.min(minX, p.getX());
                    minY = Math.min(minY, p.getY());
                    maxX = Math.max(maxX, p.getX());
                    maxY = Math.max(maxY, p.getY());
                }
                this.mbr = new Rectangle(new Point(minX, minY), new Point(maxX, maxY));
            } else {
                if (children.isEmpty()) {
                    this.mbr = createInvalidMbr();
                    return;
                }

                Node c = children.stream().filter(Node::hasValidMbr).findFirst().orElse(null);
                if(c == null) {
                    this.mbr = createInvalidMbr();
                    return;
                }

                double minX = c.mbr.getLeftTop().getX();
                double minY = c.mbr.getLeftTop().getY();
                double maxX = c.mbr.getRightBottom().getX();
                double maxY = c.mbr.getRightBottom().getY();

                for (int i = 0; i < children.size(); i++) {
                    c = children.get(i);
                    if (!c.hasValidMbr())
                        continue;
                    minX = Math.min(minX, c.mbr.getLeftTop().getX());
                    minY = Math.min(minY, c.mbr.getLeftTop().getY());
                    maxX = Math.max(maxX, c.mbr.getRightBottom().getX());
                    maxY = Math.max(maxY, c.mbr.getRightBottom().getY());
                }
                this.mbr = new Rectangle(new Point(minX, minY), new Point(maxX, maxY));
            }
        }
    }

    // RTreePanel 내부 클래스. Swing의 JPanel을 상속받아 R-Tree를 화면에 그림.
    class RTreePanel extends JPanel {
        private final int PADDING = 50;
        private final Color[] LEVEL_COLORS = {
                Color.RED, Color.ORANGE, Color.YELLOW, Color.GREEN, Color.BLUE, Color.MAGENTA
        };
        private double dataMaxX = 200;
        private double dataMaxY = 200;

        @Override
        protected void paintComponent(Graphics g) {
            super.paintComponent(g);
            Graphics2D g2d = (Graphics2D) g;
            g2d.setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON);

            int panelWidth = getWidth();
            int panelHeight = getHeight();
            double scaleX = (panelWidth - 2 * PADDING) / dataMaxX;
            double scaleY = (panelHeight - 2 * PADDING) / dataMaxY;
            double scale = Math.min(scaleX, scaleY);
            int yOffset = panelHeight - PADDING;

            if (root != null) {
                drawNode(g2d, root, 0, scale, yOffset);
            }

            if (currentSearchRect != null) {
                g2d.setColor(new Color(0, 0, 255, 50));
                int x = (int) (currentSearchRect.getLeftTop().getX() * scale) + PADDING;
                int y = yOffset - (int) (currentSearchRect.getRightBottom().getY() * scale);
                int w = (int) ((currentSearchRect.getRightBottom().getX() - currentSearchRect.getLeftTop().getX())
                        * scale);
                int h = (int) ((currentSearchRect.getRightBottom().getY() - currentSearchRect.getLeftTop().getY())
                        * scale);
                g2d.fillRect(x, y, w, h);
                g2d.setColor(Color.BLUE);
                g2d.drawRect(x, y, w, h);
            }

            if (currentKnnSource != null) {
                g2d.setColor(Color.RED);
                int x = (int) (currentKnnSource.getX() * scale) + PADDING - 4;
                int y = yOffset - (int) (currentKnnSource.getY() * scale) - 4;
                g2d.fillOval(x, y, 8, 8);
            }

            g2d.setColor(Color.CYAN);
            List<Point> pointsToHighlight = new ArrayList<>(highlightedPoints);
            for (Point p : pointsToHighlight) {
                int x = (int) (p.getX() * scale) + PADDING - 5;
                int y = yOffset - (int) (p.getY() * scale) - 5;
                g2d.fillOval(x, y, 10, 10);
            }
        }

        private void drawNode(Graphics2D g, Node node, int level, double scale, int yOffset) {
            if (node == null || !node.hasValidMbr())
                return;

            Rectangle mbr = node.mbr;
            int x = (int) (mbr.getLeftTop().getX() * scale) + PADDING;
            int y = yOffset - (int) (mbr.getRightBottom().getY() * scale);
            int w = (int) ((mbr.getRightBottom().getX() - mbr.getLeftTop().getX()) * scale);
            int h = (int) ((mbr.getRightBottom().getY() - mbr.getLeftTop().getY()) * scale);
            Color c = LEVEL_COLORS[level % LEVEL_COLORS.length];

            if (currentSearchRect != null && rectIntersects(node.getMbr(), currentSearchRect)) {
                g.setColor(new Color(c.getRed(), c.getGreen(), c.getBlue(), 100));
            } else if (currentSearchRect != null) {
                g.setColor(new Color(200, 200, 200, 30));
            } else {
                g.setColor(new Color(c.getRed(), c.getGreen(), c.getBlue(), 50));
            }

            g.fillRect(x, y, w, h);
            g.setColor(c);
            g.drawRect(x, y, w, h);

            if (node.leaf) {
                g.setColor(Color.BLACK);
                for (Point p : node.points) {
                    int px = (int) (p.getX() * scale) + PADDING - 2;
                    int py = yOffset - (int) (p.getY() * scale) - 2;
                    g.fillOval(px, py, 4, 4);
                }
            } else {
                for (Node child : node.children) {
                    drawNode(g, child, level + 1, scale, yOffset);
                }
            }
        }
    }

    // DistSpat 내부 클래스. KNN 검색 시 우선순위 큐(PQ)에 거리와 객체를 함께 저장.
    private class DistSpat implements Comparable<DistSpat> {
        final double dist;
        final Object item;
        DistSpat(Object item, double dist) { this.item = item; this.dist = dist; }
        @Override public int compareTo(DistSpat other) { return Double.compare(this.dist, other.dist); }
    }

    // RTreeImpl 생성자. Assignment45가 new RTreeImpl()을 호출할 때 GUI 창을 생성.
    public RTreeImpl() {
        this.root = new Node(true, null);
        this.size = 0;

        SwingUtilities.invokeLater(() -> {
            this.guiFrame = new JFrame("R-Tree 시각화 (Assignment 45) - Quadratic Split");
            this.guiPanel = new RTreePanel();
            this.guiFrame.add(this.guiPanel);
            this.guiFrame.setSize(800, 800);
            this.guiFrame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
            this.guiFrame.setVisible(true);
        });
    }

    // updateGUI 헬퍼 메서드. GUI를 갱신할 때 스레드 문제를 해결(EDT에서 실행).
    private void updateGUI() {
        if (this.guiPanel != null) {
            SwingUtilities.invokeLater(() -> {
                guiPanel.repaint();
            });
        }
    }

    // add 메서드. 포인트를 삽입하고, Thread.sleep으로 애니메이션 효과를 줌.
    @Override
    public void add(Point point) {
        this.currentSearchRect = null;
        this.currentKnnSource = null;
        this.highlightedPoints.clear();
        if (findLeaf(root, point) != null) {
            return;
        }
        Node leaf = chooseLeaf(root, point);
        insert(leaf, point);
        this.size++;
        updateGUI();

        // Thread.sleep() 호출. InterruptedException 예외 처리가 필요.
        try {
            Thread.sleep(3000);
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
    }

    // search 메서드. 범위 검색을 수행하고, Task 1 완료를 JOptionPane으로 알림.
    @Override
    public Iterator<Point> search(Rectangle rectangle) {
        this.currentSearchRect = null;
        this.currentKnnSource = null;
        this.highlightedPoints.clear();
        updateGUI();

        // JOptionPane 호출. Assignment45의 main 스레드를 여기서 일시정지시킴.
        JOptionPane.showMessageDialog(guiFrame,
                "Task 1 complete\n",
                "Task 1 complete", JOptionPane.INFORMATION_MESSAGE);

        List<Point> result = new ArrayList<>();
        this.currentSearchRect = rectangle;
        this.highlightedPoints.clear();
        searchRecursive(root, rectangle, result);
        this.highlightedPoints.addAll(result);
        updateGUI();

        return result.iterator();
    }

    // nearest 메서드. KNN 검색을 수행하고, Task 2 완료를 JOptionPane으로 알림.
    @Override
    public Iterator<Point> nearest(Point source, int maxCount) {
        updateGUI();

        JOptionPane.showMessageDialog(guiFrame,
                "Task 2 complete\n",
                "Task 2 완료", JOptionPane.INFORMATION_MESSAGE);

        PriorityQueue<DistSpat> pq = new PriorityQueue<>();
        pq.add(new DistSpat(root, 0.0));
        List<Point> result = new ArrayList<>();
        this.currentSearchRect = null;
        this.currentKnnSource = source;
        this.highlightedPoints.clear();

        while (!pq.isEmpty() && result.size() < maxCount) {
            DistSpat current = pq.poll();
            if (current.item instanceof Point) {
                result.add((Point) current.item);
            } else {
                Node node = (Node) current.item;
                if (node.leaf) {
                    for (Point p : node.points) {
                        pq.add(new DistSpat(p, rectMinDistance(new Rectangle(p,p), source)));
                    }
                } else {
                    for (Node child : node.children) {
                        if (child.hasValidMbr()) {
                            pq.add(new DistSpat(child, rectMinDistance(child.getMbr(), source)));
                        }
                    }
                }
            }
        }
        this.highlightedPoints.addAll(result);
        updateGUI();

        return result.iterator();
    }

    // delete 메서드. 포인트를 삭제하고, 첫 호출 시 Task 3 완료를 알림.
    @Override
    public void delete(Point point) {
        if (firstDeleteCall) {
            firstDeleteCall = false;
            updateGUI();
            JOptionPane.showMessageDialog(guiFrame,
                    "Task 3 complete\n",
                    "Task 3 complete", JOptionPane.INFORMATION_MESSAGE);

            this.currentSearchRect = null;
            this.currentKnnSource = null;
            this.highlightedPoints.clear();
        }

        Node leaf = findLeaf(root, point);
        if (leaf == null) {
            return;
        }
        Point toRemove = null;
        for(Point p : leaf.points) {
            if(p.getX() == point.getX() && p.getY() == point.getY()) {
                toRemove = p;
                break;
            }
        }
        if (toRemove == null) {
            return;
        }

        leaf.points.remove(toRemove);
        leaf.recalcMbr();
        condenseTree(leaf);
        this.size--;

        if (size == 0) {
            root = new Node(true, null);
        }
        updateGUI();

        // Thread.sleep() 호출. 삭제 과정 애니메이션을 위해 1.5초 대기.
        try {
            Thread.sleep(3000);
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
    }

    // isEmpty 메서드. 모든 Task 완료 후 최종 결과를 JOptionPane으로 알림.
    @Override
    public boolean isEmpty() {
        updateGUI();
        boolean result = (this.size == 0);

        JOptionPane.showMessageDialog(guiFrame,
                "Task 4 complete" +
                        "최종 결과: isEmpty() = " + result,
                "Task 4 complete", JOptionPane.INFORMATION_MESSAGE);

        return result;
    }

    // chooseLeaf 메서드. 면적 증가(enlargement)가 가장 적은 하위 노드를 선택.
    private Node chooseLeaf(Node node, Point point) {
        if (node.leaf) {
            return node;
        }
        Node bestChild = null;
        double minEnlargement = Double.POSITIVE_INFINITY;

        for (Node child : node.children) {
            double enlargement = rectEnlargement(child.getMbr(), point);

            if (enlargement < minEnlargement) {
                minEnlargement = enlargement;
                bestChild = child;
            } else if (enlargement == minEnlargement) {
                if (bestChild == null || rectArea(child.getMbr()) < rectArea(bestChild.getMbr())) {
                    bestChild = child;
                }
            }
        }
        if (bestChild == null) {
            bestChild = node.children.get(0);
        }
        return chooseLeaf(bestChild, point);
    }

    // insert 메서드. 리프에 삽입 후, 오버플로우 시 splitNode를 호출.
    private void insert(Node leaf, Point point) {
        leaf.points.add(point);
        leaf.recalcMbr();
        if (leaf.points.size() > MAX_ENTRIES) {
            Node[] newNodes = splitNode(leaf);
            adjustTree(newNodes[0], newNodes[1]);
        } else {
            adjustTree(leaf, null);
        }
    }

    // splitNode 메서드. Quadratic Split(2차 분할) 알고리즘을 구현.
    private Node[] splitNode(Node node) {
        List entries;
        if (node.leaf) {
            entries = new ArrayList<>(node.points);
        } else {
            entries = new ArrayList<>(node.children);
        }
        Node group1 = node;
        Node group2 = new Node(node.leaf, node.parent);
        Object[] seeds = pickSeeds(entries, node);
        Object seed1 = seeds[0];
        Object seed2 = seeds[1];

        if (node.leaf) {
            group1.points.clear();
            group1.points.add((Point) seed1);
            group2.points.add((Point) seed2);
        } else {
            group1.children.clear();
            group1.children.add((Node) seed1);
            ((Node)seed1).parent = group1;
            group2.children.add((Node) seed2);
            ((Node)seed2).parent = group2;
        }

        entries.remove(seed1);
        entries.remove(seed2);

        while (!entries.isEmpty()) {
            // m=2 (최소 엔트리) 보장 로직.
            if (group1.leaf) {
                if (group1.points.size() + entries.size() == MIN_ENTRIES) {
                    group1.points.addAll(entries);
                    entries.clear();
                    break;
                }
                if (group2.points.size() + entries.size() == MIN_ENTRIES) {
                    group2.points.addAll(entries);
                    entries.clear();
                    break;
                }
            } else {
                if (group1.children.size() + entries.size() == MIN_ENTRIES) {
                    group1.children.addAll(entries);
                    entries.forEach(e -> ((Node)e).parent = group1);
                    entries.clear();
                    break;
                }
                if (group2.children.size() + entries.size() == MIN_ENTRIES) {
                    group2.children.addAll(entries);
                    entries.forEach(e -> ((Node)e).parent = group2);
                    entries.clear();
                    break;
                }
            }

            Object nextEntry = pickNext(entries, group1, group2, node);
            Rectangle mbr1 = group1.getMbr();
            Rectangle mbr2 = group2.getMbr();
            Rectangle entryMbr = node.getEntryMbr(nextEntry);

            double cost1 = rectEnlargement(mbr1, entryMbr);
            double cost2 = rectEnlargement(mbr2, entryMbr);

            if (cost1 < cost2) {
                if (node.leaf) group1.points.add((Point) nextEntry);
                else { group1.children.add((Node) nextEntry); ((Node)nextEntry).parent = group1; }
            } else if (cost2 < cost1) {
                if (node.leaf) group2.points.add((Point) nextEntry);
                else { group2.children.add((Node) nextEntry); ((Node)nextEntry).parent = group2; }
            } else {
                if (rectArea(mbr1) < rectArea(mbr2)) {
                    if (node.leaf) group1.points.add((Point) nextEntry);
                    else { group1.children.add((Node) nextEntry); ((Node)nextEntry).parent = group1; }
                } else if (rectArea(mbr2) < rectArea(mbr1)) {
                    if (node.leaf) group2.points.add((Point) nextEntry);
                    else { group2.children.add((Node) nextEntry); ((Node)nextEntry).parent = group2; }
                } else {
                    int size1 = node.leaf ? group1.points.size() : group1.children.size();
                    int size2 = node.leaf ? group2.points.size() : group2.children.size();
                    if (size1 <= size2) {
                        if (node.leaf) group1.points.add((Point) nextEntry);
                        else { group1.children.add((Node) nextEntry); ((Node)nextEntry).parent = group1; }
                    } else {
                        if (node.leaf) group2.points.add((Point) nextEntry);
                        else { group2.children.add((Node) nextEntry); ((Node)nextEntry).parent = group2; }
                    }
                }
            }

            group1.recalcMbr();
            group2.recalcMbr();
            entries.remove(nextEntry);
        }
        group1.recalcMbr();
        group2.recalcMbr();
        return new Node[] { group1, group2 };
    }

    // pickSeeds 헬퍼 메서드. Quadratic Split의 첫 단계로, 가장 낭비되는 공간이 큰 두 시드를 고름.
    private Object[] pickSeeds(List entries, Node node) {
        Object seed1 = null;
        Object seed2 = null;
        double maxWastedArea = Double.NEGATIVE_INFINITY;

        for (int i = 0; i < entries.size(); i++) {
            for (int j = i + 1; j < entries.size(); j++) {
                Object e1 = entries.get(i);
                Object e2 = entries.get(j);
                Rectangle mbr1 = node.getEntryMbr(e1);
                Rectangle mbr2 = node.getEntryMbr(e2);

                Rectangle mergedMbr = rectMerge(mbr1, mbr2);
                double wastedArea = rectArea(mergedMbr) - rectArea(mbr1) - rectArea(mbr2);

                if (wastedArea > maxWastedArea) {
                    maxWastedArea = wastedArea;
                    seed1 = e1;
                    seed2 = e2;
                }
            }
        }
        return new Object[] { seed1, seed2 };
    }

    // pickNext 헬퍼 메서드. Quadratic Split의 두 번째 단계로, 그룹 선호도 차이가 가장 큰 엔트리를 고름.
    private Object pickNext(List entries, Node group1, Node group2, Node node) {
        Object nextEntry = null;
        double maxDiff = Double.NEGATIVE_INFINITY;
        Rectangle mbr1 = group1.getMbr();
        Rectangle mbr2 = group2.getMbr();

        for (Object entry : entries) {
            Rectangle entryMbr = node.getEntryMbr(entry);
            double cost1 = rectEnlargement(mbr1, entryMbr);
            double cost2 = rectEnlargement(mbr2, entryMbr);
            double diff = Math.abs(cost1 - cost2);

            if (diff > maxDiff) {
                maxDiff = diff;
                nextEntry = entry;
            }
        }
        return nextEntry;
    }

    // adjustTree 메서드. 삽입/분할 후 트리를 재조정. (루트 MBR 버그 수정된 버전)
    private void adjustTree(Node node, Node newNode) {
        Node n = node;
        Node nn = newNode;
        while (n != root) {
            Node parent = n.parent;
            if (parent == null) break;

            // 핵심 로직. 자식(nn)을 먼저 추가하고, MBR을 재계산해야 .
            if (nn != null) {
                parent.children.add(nn);
                nn.parent = parent;
            }
            parent.recalcMbr();

            if (parent.children.size() > MAX_ENTRIES) {
                Node[] splitParents = splitNode(parent);
                n = splitParents[0];
                nn = splitParents[1];
            } else {
                n = parent;
                nn = null;
            }
        }

        // 루트 분할 처리 로직.
        if (nn != null) {
            Node newRoot = new Node(false, null);
            newRoot.children.add(n);
            newRoot.children.add(nn);
            n.parent = newRoot;
            nn.parent = newRoot;
            newRoot.recalcMbr();
            this.root = newRoot;
        }
    }

    // searchRecursive 헬퍼 메서드. MBR이 겹치는지(intersects) 확인하여 가지치기(Pruning)를 수행.
    private void searchRecursive(Node node, Rectangle rectangle, List<Point> result) {
        if (node.leaf) {
            for (Point p : node.points) {
                if (rectContains(rectangle, p)) {
                    result.add(p);
                }
            }
        } else {
            for (Node child : node.children) {
                if (rectIntersects(child.getMbr(), rectangle)) {
                    searchRecursive(child, rectangle, result);
                }
            }
        }
    }

    // findLeaf 헬퍼 메서드. 삭제할 포인트가 어느 리프에 있는지 찾음.
    private Node findLeaf(Node node, Point point) {
        if (node.leaf) {
            for (Point p : node.points) {
                if (p.getX() == point.getX() && p.getY() == point.getY()) {
                    return node;
                }
            }
            return null;
        }
        for (Node child : node.children) {
            if (rectContains(child.getMbr(), point)) {
                Node result = findLeaf(child, point);
                if (result != null) {
                    return result;
                }
            }
        }
        return null;
    }

    // condenseTree 메서드. 삭제 후 트리를 압축(언더플로우 처리, MBR 축소).
    private void condenseTree(Node node) {
        Node n = node;
        while (n != root) {
            Node parent = n.parent;
            if (n.leaf && n.points.size() < MIN_ENTRIES) {
                handleUnderflow(n);
            } else if (!n.leaf && n.children.size() < MIN_ENTRIES) {
                handleUnderflow(n);
            } else {
                n.recalcMbr();
            }
            if(parent == null) break;

            // handleUnderflow에서 n이 제거됐는지 확인 후 부모로 이동.
            if(parent.children.contains(n)) {
                n = parent;
            } else {
                n = parent;
            }
        }

        // 루트 높이 축소 로직.
        if (!root.leaf && root.children.size() == 1) {
            Node oldRoot = root;
            root = root.children.get(0);
            root.parent = null;
            oldRoot.children.clear();
        }
    }

    // handleUnderflow 헬퍼 메서드. m=2개 미만인 노드를 형제와 병합(Merge).
    private void handleUnderflow(Node node) {
        Node parent = node.parent;
        if (parent == null) return;
        Node sibling = null;
        for (Node s : parent.children) {
            if (s != node) {
                sibling = s;
                break;
            }
        }
        if (sibling == null) {
            return;
        }

        // (재분배(Re-distribution)는 생략하고 병합(Merge)만 구현)
        if (node.leaf) {
            if (sibling.points.size() + node.points.size() <= MAX_ENTRIES) {
                sibling.points.addAll(node.points);
                parent.children.remove(node);
                node.points.clear();
                sibling.recalcMbr();
            } else {
                node.recalcMbr();
            }
        } else {
            if (sibling.children.size() + node.children.size() <= MAX_ENTRIES) {
                sibling.children.addAll(node.children);
                for (Node child : node.children) {
                    child.parent = sibling;
                }
                parent.children.remove(node);
                node.children.clear();
                sibling.recalcMbr();
            } else {
                node.recalcMbr();
            }
        }
    }

    // -----------------------------------------------------------------
    // 5. Rectangle 헬퍼 메서드
    // -----------------------------------------------------------------

    // createInvalidMbr 헬퍼 메서드. 비어있는 MBR을 정의.
    private Rectangle createInvalidMbr() {
        return new Rectangle(
                new Point(Double.POSITIVE_INFINITY, Double.POSITIVE_INFINITY),
                new Point(Double.NEGATIVE_INFINITY, Double.NEGATIVE_INFINITY));
    }

    // rectArea 헬퍼 메서드. 사각형의 면적을 계산.
    private double rectArea(Rectangle r) {
        if (r.getLeftTop().getX() == Double.POSITIVE_INFINITY) {
            return 0;
        }
        double width = r.getRightBottom().getX() - r.getLeftTop().getX();
        double height = r.getRightBottom().getY() - r.getLeftTop().getY();
        return width * height;
    }

    // rectContains 헬퍼 메서드. 사각형이 점을 포하는지 확인.
    private boolean rectContains(Rectangle r, Point p) {
        if (r == null || p == null || r.getLeftTop().getX() == Double.POSITIVE_INFINITY) {
            return false;
        }
        return p.getX() >= r.getLeftTop().getX() &&
                p.getX() <= r.getRightBottom().getX() &&
                p.getY() >= r.getLeftTop().getY() &&
                p.getY() <= r.getRightBottom().getY();
    }

    // rectIntersects 헬퍼 메서드. 두 사각형이 겹치는지 확인.
    private boolean rectIntersects(Rectangle r1, Rectangle r2) {
        if (r1 == null || r2 == null) return false;
        if (r1.getLeftTop().getX() == Double.POSITIVE_INFINITY ||
                r2.getLeftTop().getX() == Double.POSITIVE_INFINITY) {
            return false;
        }
        return !(r2.getRightBottom().getX() < r1.getLeftTop().getX() ||
                r2.getLeftTop().getX() > r1.getRightBottom().getX() ||
                r2.getRightBottom().getY() < r1.getLeftTop().getY() ||
                r2.getLeftTop().getY() > r1.getRightBottom().getY());
    }

    // rectEnlargement 헬퍼 메서드. 점을 포할 때 면적 증가량을 계산.
    private double rectEnlargement(Rectangle r, Point p) {
        if (p == null) return 0;
        if (r.getLeftTop().getX() == Double.POSITIVE_INFINITY) {
            return 0;
        }
        double newMinX = Math.min(r.getLeftTop().getX(), p.getX());
        double newMinY = Math.min(r.getLeftTop().getY(), p.getY());
        double newMaxX = Math.max(r.getRightBottom().getX(), p.getX());
        double newMaxY = Math.max(r.getRightBottom().getY(), p.getY());
        double newArea = (newMaxX - newMinX) * (newMaxY - newMinY);
        return newArea - rectArea(r);
    }

    // rectEnlargement 헬퍼 메서드 오버로딩. 사각형을 포할 때 면적 증가량을 계산.
    private double rectEnlargement(Rectangle r1, Rectangle r2) {
        if (r2 == null || r2.getLeftTop().getX() == Double.POSITIVE_INFINITY) {
            return 0;
        }
        if (r1.getLeftTop().getX() == Double.POSITIVE_INFINITY) {
            return rectArea(r2);
        }
        double newMinX = Math.min(r1.getLeftTop().getX(), r2.getLeftTop().getX());
        double newMinY = Math.min(r1.getLeftTop().getY(), r2.getLeftTop().getY());
        double newMaxX = Math.max(r1.getRightBottom().getX(), r2.getRightBottom().getX());
        double newMaxY = Math.max(r1.getRightBottom().getY(), r2.getRightBottom().getY());
        double newArea = (newMaxX - newMinX) * (newMaxY - newMinY);
        return newArea - rectArea(r1);
    }

    // rectMerge 헬퍼 메서드. 두 사각형을 병합(merge)하여 새 MBR을 반환.
    private Rectangle rectMerge(Rectangle r1, Rectangle r2) {
        if (r1.getLeftTop().getX() == Double.POSITIVE_INFINITY &&
                r2.getLeftTop().getX() == Double.POSITIVE_INFINITY) {
            return createInvalidMbr();
        }
        if (r1.getLeftTop().getX() == Double.POSITIVE_INFINITY) {
            return new Rectangle(r2.getLeftTop(), r2.getRightBottom());
        }
        if (r2.getLeftTop().getX() == Double.POSITIVE_INFINITY) {
            return new Rectangle(r1.getLeftTop(), r1.getRightBottom());
        }
        double newMinX = Math.min(r1.getLeftTop().getX(), r2.getLeftTop().getX());
        double newMinY = Math.min(r1.getLeftTop().getY(), r2.getLeftTop().getY());
        double newMaxX = Math.max(r1.getRightBottom().getX(), r2.getRightBottom().getX());
        double newMaxY = Math.max(r1.getRightBottom().getY(), r2.getRightBottom().getY());
        return new Rectangle(new Point(newMinX, newMinY), new Point(newMaxX, newMaxY));
    }

    // rectMinDistance 헬퍼 메서드. 사각형과 점 사이의 최소 거리(MINDIST)를 계산.
    private double rectMinDistance(Rectangle r, Point p) {
        if (r.getLeftTop().getX() == Double.POSITIVE_INFINITY) {
            return Double.POSITIVE_INFINITY;
        }
        double dx = 0;
        double dy = 0;
        if (p.getX() < r.getLeftTop().getX()) {
            dx = r.getLeftTop().getX() - p.getX();
        } else if (p.getX() > r.getRightBottom().getX()) {
            dx = p.getX() - r.getRightBottom().getX();
        }
        if (p.getY() < r.getLeftTop().getY()) {
            dy = r.getLeftTop().getY() - p.getY();
        } else if (p.getY() > r.getRightBottom().getY()) {
            dy = p.getY() - r.getRightBottom().getY();
        }
        if (dx == 0 && dy == 0) return 0.0;
        return Math.sqrt(dx * dx + dy * dy);
    }
}
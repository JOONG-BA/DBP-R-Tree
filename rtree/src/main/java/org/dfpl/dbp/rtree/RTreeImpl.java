package org.dfpl.dbp.rtree.team1;

import java.util.Iterator;
import java.util.List;
import java.util.ArrayList;
import java.util.Map;
import java.util.HashMap;
import java.util.PriorityQueue;

import java.awt.Color;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.RenderingHints;
import java.awt.BasicStroke;
import java.awt.Font;
import javax.swing.JFrame;
import javax.swing.JPanel;
import javax.swing.SwingUtilities;
import javax.swing.JOptionPane;

/**
 * RTree 구현 클래스.
 * R-Tree의 핵심 로직(삽입, 검색, 삭제)과 Java Swing을 이용한 시각화 기능을 포함함.
 */
public class RTreeImpl implements RTree {

    private static final int MAX_ENTRIES = 4;
    private static final int MIN_ENTRIES = 2;

    private Node root;
    private int size;

    private JFrame guiFrame;
    private RTreePanel guiPanel;

    private Rectangle currentSearchRect;
    private Point currentKnnSource;
    private List<Point> highlightedPoints = new ArrayList<>();
    private boolean firstDeleteCall = true;

    private Point lastInsertedPoint;
    private Rectangle lastExpandedMbr;
    private Node splitGroup1;
    private Node splitGroup2;
    private List<Node> prunedNodes = new ArrayList<>();

    private List<Node> knnVisitedNodes = new ArrayList<>();
    private Map<Node, Integer> knnVisitOrder = new HashMap<>();
    private Node knnCurrentNode;
    private double knnCurrentBestDist = Double.POSITIVE_INFINITY;
    private List<Point> knnCandidatePoints = new ArrayList<>();
    private Map<Point, Double> knnResultDistances = new HashMap<>();
    private Point knnNewlyFoundPoint;

    private Point deletingPoint;
    private Node deletingLeafNode;
    private Rectangle oldMbrBeforeDelete;
    private Rectangle shrinkingMbr;
    private List<Node> underflowNodes = new ArrayList<>();

    /**
     * R-Tree의 노드 클래스.
     * 사각형(MBR) 정보와 자식 노드 또는 포인트 리스트를 관리함.
     */
    class Node {
        Rectangle mbr;
        boolean leaf;
        List<Node> children;
        List<Point> points;
        Node parent;

        /**
         * Node 생성자.
         * 리프 노드 여부와 부모 노드를 받아 노드를 초기화함.
         */
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

        /**
         * MBR 반환 메서드.
         * 현재 노드의 MBR을 반환하며, 초기화되지 않았을 경우 무효한 MBR을 반환함.
         */
        public Rectangle getMbr() {
            if (!hasValidMbr()) {
                return createInvalidMbr();
            }
            return this.mbr;
        }

        /**
         * 엔트리 MBR 반환 메서드.
         * 포인트나 자식 노드 객체를 받아 해당 객체의 MBR을 반환함.
         */
        public Rectangle getEntryMbr(Object entry) {
            if (entry instanceof Point) {
                Point p = (Point) entry;
                return new Rectangle(p, p);
            } else if (entry instanceof Node) {
                return ((Node) entry).getMbr();
            }
            return createInvalidMbr();
        }

        /**
         * MBR 유효성 확인 메서드.
         * 현재 MBR이 유효한 값을 가지고 있는지 확인함.
         */
        public boolean hasValidMbr() {
            return mbr.getLeftTop().getX() != Double.POSITIVE_INFINITY;
        }

        /**
         * MBR 재계산 메서드.
         * 노드가 포함하고 있는 자식들이나 포인트들을 기반으로 MBR을 다시 계산하여 갱신함.
         */
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

    /**
     * 시각화 패널 클래스.
     * R-Tree의 상태와 알고리즘 동작 과정을 그래픽으로 그림.
     */
    class RTreePanel extends JPanel {
        private final int PADDING = 60;
        private final Color COLOR_ROOT = new Color(148, 0, 211);
        private final Color COLOR_INTERNAL = new Color(0, 0, 255);
        private final Color COLOR_LEAF = new Color(0, 128, 0);
        private double dataMaxX = 200;
        private double dataMaxY = 200;

        /**
         * 컴포넌트 그리기 메서드.
         * 그래픽 객체를 받아 배경, 격자, 트리 노드, 시각화 효과 등을 순서대로 그림.
         */
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

            drawGrid(g2d, scale, yOffset, panelWidth, panelHeight);

            if (root != null) {
                drawDepthMBR(g2d, root, 0, scale, yOffset);
            }

            if (splitGroup1 != null && splitGroup1.hasValidMbr()) {
                drawSplitOverlay(g2d, splitGroup1, new Color(0, 180, 255, 70), scale, yOffset, "Group 1");
            }
            if (splitGroup2 != null && splitGroup2.hasValidMbr()) {
                drawSplitOverlay(g2d, splitGroup2, new Color(255, 120, 200, 70), scale, yOffset, "Group 2");
            }

            if (currentSearchRect != null) {
                drawPrunedNodes(g2d, scale, yOffset);
                drawSearchArea(g2d, scale, yOffset);
            }

            drawKNNVisualization(g2d, scale, yOffset);

            if (deletingLeafNode != null) {
                drawDeletingLeaf(g2d, scale, yOffset);
            }

            if (oldMbrBeforeDelete != null && shrinkingMbr != null) {
                drawShrinkAnimation(g2d, scale, yOffset);
            }

            if (lastExpandedMbr != null && splitGroup1 == null && splitGroup2 == null) {
                drawExpandedMBR(g2d, scale, yOffset);
            }

            if (root != null) {
                drawAllPoints(g2d, root, scale, yOffset);
            }

            drawHighlightedPoints(g2d, scale, yOffset);

            if (lastInsertedPoint != null) {
                drawNewPoint(g2d, scale, yOffset);
            }

            if (deletingPoint != null) {
                drawDeletingPoint(g2d, scale, yOffset);
            }
        }

        /**
         * 배경 격자 그리기 메서드.
         * 좌표계의 눈금과 축을 그림.
         */
        private void drawGrid(Graphics2D g, double scale, int yOffset, int panelWidth, int panelHeight) {
            g.setColor(new Color(220, 220, 220));
            g.setStroke(new BasicStroke(1));

            for (int i = 0; i <= 200; i += 20) {
                int x = (int) (i * scale) + PADDING;
                g.drawLine(x, PADDING, x, yOffset);
                g.setColor(Color.DARK_GRAY);
                g.drawString(String.valueOf(i), x - 8, yOffset + 15);
                g.setColor(new Color(220, 220, 220));
            }

            for (int i = 0; i <= 200; i += 20) {
                int y = yOffset - (int) (i * scale);
                g.drawLine(PADDING, y, panelWidth - PADDING, y);
                g.setColor(Color.DARK_GRAY);
                g.drawString(String.valueOf(i), PADDING - 25, y + 4);
                g.setColor(new Color(220, 220, 220));
            }

            g.setColor(Color.BLACK);
            g.setStroke(new BasicStroke(2));
            g.drawLine(PADDING, yOffset, panelWidth - PADDING, yOffset);
            g.drawLine(PADDING, PADDING, PADDING, yOffset);
            g.setStroke(new BasicStroke(1));
        }

        /**
         * MBR 그리기 메서드.
         * 트리의 깊이에 따라 다른 색상으로 노드의 MBR을 재귀적으로 그림.
         */
        private void drawDepthMBR(Graphics2D g, Node node, int depth, double scale, int yOffset) {
            if (node == null || !node.hasValidMbr()) return;

            Rectangle mbr = node.getMbr();
            int x = (int) (mbr.getLeftTop().getX() * scale) + PADDING;
            int y = yOffset - (int) (mbr.getRightBottom().getY() * scale);
            int w = (int) ((mbr.getRightBottom().getX() - mbr.getLeftTop().getX()) * scale);
            int h = (int) ((mbr.getRightBottom().getY() - mbr.getLeftTop().getY()) * scale);

            if (node == root) {
                g.setColor(new Color(148, 0, 211, 20));
                g.fillRect(x, y, w, h);
                g.setColor(new Color(148, 0, 211, 100));
                g.setStroke(new BasicStroke(1.5f));
                g.drawRect(x, y, w, h);
                g.setStroke(new BasicStroke(1));
            } else if (node.leaf) {
                g.setColor(new Color(0, 180, 0, 25));
                g.fillRect(x, y, w, h);
                g.setColor(new Color(0, 150, 0, 120));
                g.setStroke(new BasicStroke(1.0f));
                g.drawRect(x, y, w, h);
                g.setStroke(new BasicStroke(1));
            } else {
                g.setColor(new Color(0, 120, 255, 20));
                g.fillRect(x, y, w, h);
                g.setColor(new Color(0, 100, 255, 100));
                g.setStroke(new BasicStroke(1.0f));
                g.drawRect(x, y, w, h);
                g.setStroke(new BasicStroke(1));
            }

            if (!node.leaf && node.children != null) {
                for (Node child : node.children) {
                    drawDepthMBR(g, child, depth + 1, scale, yOffset);
                }
            }
        }

        /**
         * 분할 시각화 메서드.
         * 노드 분할 시 두 그룹을 서로 다른 색상으로 강조하여 그림.
         */
        private void drawSplitOverlay(Graphics2D g, Node node, Color color, double scale, int yOffset, String label) {
            Rectangle mbr = node.getMbr();
            int x = (int) (mbr.getLeftTop().getX() * scale) + PADDING;
            int y = yOffset - (int) (mbr.getRightBottom().getY() * scale);
            int w = (int) ((mbr.getRightBottom().getX() - mbr.getLeftTop().getX()) * scale);
            int h = (int) ((mbr.getRightBottom().getY() - mbr.getLeftTop().getY()) * scale);

            g.setColor(color);
            g.fillRect(x, y, w, h);
            g.setColor(new Color(color.getRed(), color.getGreen(), color.getBlue(), 200));
            g.setStroke(new BasicStroke(2));
            g.drawRect(x, y, w, h);
            g.setStroke(new BasicStroke(1));

            g.setColor(Color.BLACK);
            g.setFont(new Font("SansSerif", Font.BOLD, 12));
            g.drawString(label, x + w/2 - 20, y + h/2);
        }

        /**
         * 검색 영역 그리기 메서드.
         * 사용자가 요청한 범위 검색 사각형을 그림.
         */
        private void drawSearchArea(Graphics2D g, double scale, int yOffset) {
            int x = (int) (currentSearchRect.getLeftTop().getX() * scale) + PADDING;
            int y = yOffset - (int) (currentSearchRect.getRightBottom().getY() * scale);
            int w = (int) ((currentSearchRect.getRightBottom().getX() - currentSearchRect.getLeftTop().getX()) * scale);
            int h = (int) ((currentSearchRect.getRightBottom().getY() - currentSearchRect.getLeftTop().getY()) * scale);

            g.setColor(new Color(100, 150, 255, 50));
            g.fillRect(x, y, w, h);
            g.setColor(new Color(0, 100, 255));
            g.setStroke(new BasicStroke(2));
            g.drawRect(x, y, w, h);
            g.setStroke(new BasicStroke(1));
        }

        /**
         * 가지치기 노드 시각화 메서드.
         * 검색 과정에서 제외된(pruned) 노드들을 회색 빗금으로 표시함.
         */
        private void drawPrunedNodes(Graphics2D g, double scale, int yOffset) {
            g.setFont(new Font("SansSerif", Font.BOLD, 10));
            for (Node pruned : new ArrayList<>(prunedNodes)) {
                if (!pruned.hasValidMbr()) continue;

                Rectangle mbr = pruned.getMbr();
                int x = (int) (mbr.getLeftTop().getX() * scale) + PADDING;
                int y = yOffset - (int) (mbr.getRightBottom().getY() * scale);
                int w = (int) ((mbr.getRightBottom().getX() - mbr.getLeftTop().getX()) * scale);
                int h = (int) ((mbr.getRightBottom().getY() - mbr.getLeftTop().getY()) * scale);

                g.setColor(new Color(150, 150, 150, 80));
                g.fillRect(x, y, w, h);

                g.setColor(new Color(100, 100, 100, 150));
                g.setStroke(new BasicStroke(1));
                for (int i = 0; i < w + h; i += 10) {
                    int x1 = x + Math.min(i, w);
                    int y1 = y + Math.max(0, i - w);
                    int x2 = x + Math.max(0, i - h);
                    int y2 = y + Math.min(i, h);
                    g.drawLine(x1, y1, x2, y2);
                }

                g.setColor(new Color(200, 0, 0));
                g.setStroke(new BasicStroke(3));
                g.drawLine(x + 5, y + 5, x + w - 5, y + h - 5);
                g.drawLine(x + w - 5, y + 5, x + 5, y + h - 5);
                g.setStroke(new BasicStroke(1));

                g.setColor(Color.RED);
                g.drawString("PRUNED", x + w/2 - 25, y + h/2);

                drawPrunedPoints(g, pruned, scale, yOffset);
            }
        }

        /**
         * 삭제 대상 리프 시각화 메서드.
         * 삭제될 포인트가 포함된 리프 노드를 강조하여 그림.
         */
        private void drawDeletingLeaf(Graphics2D g, double scale, int yOffset) {
            if (deletingLeafNode == null || !deletingLeafNode.hasValidMbr()) return;

            Rectangle mbr = deletingLeafNode.getMbr();
            int x = (int) (mbr.getLeftTop().getX() * scale) + PADDING;
            int y = yOffset - (int) (mbr.getRightBottom().getY() * scale);
            int w = (int) ((mbr.getRightBottom().getX() - mbr.getLeftTop().getX()) * scale);
            int h = (int) ((mbr.getRightBottom().getY() - mbr.getLeftTop().getY()) * scale);

            g.setColor(new Color(255, 200, 0, 100));
            g.fillRect(x, y, w, h);
            g.setColor(new Color(255, 200, 0));
            g.setStroke(new BasicStroke(3));
            g.drawRect(x, y, w, h);
            g.setStroke(new BasicStroke(1));
        }

        /**
         * KNN 시각화 메서드.
         * 탐색 반경, 방문 노드, 후보 점, 연결선 등을 그림.
         */
        private void drawKNNVisualization(Graphics2D g, double scale, int yOffset) {
            if (currentKnnSource == null) return;

            int qx = (int) (currentKnnSource.getX() * scale) + PADDING;
            int qy = yOffset - (int) (currentKnnSource.getY() * scale);

            if (knnCurrentBestDist < Double.POSITIVE_INFINITY && knnCurrentBestDist > 0) {
                int radius = (int) (knnCurrentBestDist * scale);

                g.setColor(new Color(0, 100, 255, 10));
                g.fillOval(qx - radius, qy - radius, 2 * radius, 2 * radius);

                g.setColor(new Color(0, 50, 200));
                g.setStroke(new BasicStroke(1.5f, BasicStroke.CAP_BUTT, BasicStroke.JOIN_MITER, 10, new float[]{10, 5}, 0));
                g.drawOval(qx - radius, qy - radius, 2 * radius, 2 * radius);
                g.setStroke(new BasicStroke(1));

                g.setFont(new Font("SansSerif", Font.BOLD, 11));
                g.drawString(String.format("Dist: %.1f", knnCurrentBestDist), qx + radius + 5, qy);
            }

            g.setFont(new Font("SansSerif", Font.BOLD, 10));
            for (Node pruned : new ArrayList<>(prunedNodes)) {
                if (!pruned.hasValidMbr()) continue;
                Rectangle mbr = pruned.getMbr();
                int x = (int) (mbr.getLeftTop().getX() * scale) + PADDING;
                int y = yOffset - (int) (mbr.getRightBottom().getY() * scale);
                int w = (int) ((mbr.getRightBottom().getX() - mbr.getLeftTop().getX()) * scale);
                int h = (int) ((mbr.getRightBottom().getY() - mbr.getLeftTop().getY()) * scale);

                g.setColor(new Color(100, 100, 100, 50));
                g.fillRect(x, y, w, h);
                g.setColor(new Color(200, 0, 0));
                g.drawLine(x, y, x + w, y + h);
                g.drawLine(x + w, y, x, y + h);
                g.drawString("PRUNED", x + w/2 - 20, y + h/2);

                drawPrunedPoints(g, pruned, scale, yOffset);
            }

            g.setFont(new Font("SansSerif", Font.BOLD, 12));
            for (Node visited : new ArrayList<>(knnVisitedNodes)) {
                if (!visited.hasValidMbr() || visited == knnCurrentNode) continue;

                Rectangle mbr = visited.getMbr();
                int x = (int) (mbr.getLeftTop().getX() * scale) + PADDING;
                int y = yOffset - (int) (mbr.getRightBottom().getY() * scale);
                int w = (int) ((mbr.getRightBottom().getX() - mbr.getLeftTop().getX()) * scale);
                int h = (int) ((mbr.getRightBottom().getY() - mbr.getLeftTop().getY()) * scale);

                g.setColor(new Color(255, 140, 0, 180));
                g.setStroke(new BasicStroke(2));
                g.drawRect(x, y, w, h);
                g.setStroke(new BasicStroke(1));

                Integer order = knnVisitOrder.get(visited);
                if (order != null) {
                    g.setColor(new Color(255, 69, 0));
                    g.drawString("#" + order, x + 5, y + 15);
                }
            }

            if (knnCurrentNode != null && knnCurrentNode.hasValidMbr()) {
                Rectangle mbr = knnCurrentNode.getMbr();
                int x = (int) (mbr.getLeftTop().getX() * scale) + PADDING;
                int y = yOffset - (int) (mbr.getRightBottom().getY() * scale);
                int w = (int) ((mbr.getRightBottom().getX() - mbr.getLeftTop().getX()) * scale);
                int h = (int) ((mbr.getRightBottom().getY() - mbr.getLeftTop().getY()) * scale);

                g.setColor(new Color(255, 100, 0, 40));
                g.fillRect(x, y, w, h);

                g.setColor(new Color(255, 0, 0));
                g.setStroke(new BasicStroke(3));
                g.drawRect(x, y, w, h);
                g.setStroke(new BasicStroke(1));

                g.setColor(Color.RED);
                g.drawString("VISITING", x + 5, y - 5);
            }

            for (Point candidate : new ArrayList<>(knnCandidatePoints)) {
                int px = (int) (candidate.getX() * scale) + PADDING;
                int py = yOffset - (int) (candidate.getY() * scale);
                g.setColor(new Color(0, 180, 0));
                g.fillOval(px - 4, py - 4, 8, 8);
            }

            if (knnNewlyFoundPoint != null) {
                int px = (int) (knnNewlyFoundPoint.getX() * scale) + PADDING;
                int py = yOffset - (int) (knnNewlyFoundPoint.getY() * scale);

                g.setColor(Color.RED);
                g.setStroke(new BasicStroke(2));
                g.drawLine(qx, qy, px, py);
                g.setStroke(new BasicStroke(1));

                double dist = currentKnnSource.distance(knnNewlyFoundPoint);
                g.setFont(new Font("SansSerif", Font.BOLD, 11));
                g.setColor(Color.RED);
                g.drawString(String.format("%.2f", dist), (qx + px) / 2 + 5, (qy + py) / 2 - 5);
            }

            g.setColor(Color.RED);
            g.fillOval(qx - 6, qy - 6, 12, 12);
            g.setColor(Color.WHITE);
            g.setFont(new Font("SansSerif", Font.BOLD, 10));
            g.drawString("S", qx - 3, qy + 4);
        }

        /**
         * 가지치기 점 시각화 메서드.
         * 탐색에서 제외된 노드 내부의 점들을 회색으로 표시함.
         */
        private void drawPrunedPoints(Graphics2D g, Node node, double scale, int yOffset) {
            if (node.leaf && node.points != null) {
                for (Point p : node.points) {
                    int px = (int) (p.getX() * scale) + PADDING;
                    int py = yOffset - (int) (p.getY() * scale);

                    g.setColor(new Color(120, 120, 120));
                    g.fillOval(px - 4, py - 4, 8, 8);
                    g.setColor(new Color(80, 80, 80));
                    g.setStroke(new BasicStroke(2));
                    g.drawLine(px - 3, py - 3, px + 3, py + 3);
                    g.drawLine(px - 3, py + 3, px + 3, py - 3);
                    g.setStroke(new BasicStroke(1));
                }
            } else if (!node.leaf && node.children != null) {
                for (Node child : node.children) {
                    drawPrunedPoints(g, child, scale, yOffset);
                }
            }
        }

        /**
         * 축소 애니메이션 시각화 메서드.
         * 삭제 시 MBR이 줄어드는 과정을 이전 MBR과 새 MBR로 표시함.
         */
        private void drawShrinkAnimation(Graphics2D g, double scale, int yOffset) {
            int x1 = (int) (oldMbrBeforeDelete.getLeftTop().getX() * scale) + PADDING;
            int y1 = yOffset - (int) (oldMbrBeforeDelete.getRightBottom().getY() * scale);
            int w1 = (int) ((oldMbrBeforeDelete.getRightBottom().getX() - oldMbrBeforeDelete.getLeftTop().getX()) * scale);
            int h1 = (int) ((oldMbrBeforeDelete.getRightBottom().getY() - oldMbrBeforeDelete.getLeftTop().getY()) * scale);
            g.setColor(new Color(255, 100, 100, 150));
            g.setStroke(new BasicStroke(2, BasicStroke.CAP_BUTT, BasicStroke.JOIN_MITER, 10, new float[]{5}, 0));
            g.drawRect(x1, y1, w1, h1);

            int x2 = (int) (shrinkingMbr.getLeftTop().getX() * scale) + PADDING;
            int y2 = yOffset - (int) (shrinkingMbr.getRightBottom().getY() * scale);
            int w2 = (int) ((shrinkingMbr.getRightBottom().getX() - shrinkingMbr.getLeftTop().getX()) * scale);
            int h2 = (int) ((shrinkingMbr.getRightBottom().getY() - shrinkingMbr.getLeftTop().getY()) * scale);
            g.setColor(new Color(0, 200, 0));
            g.setStroke(new BasicStroke(2));
            g.drawRect(x2, y2, w2, h2);
            g.setStroke(new BasicStroke(1));
        }

        /**
         * 확장된 MBR 시각화 메서드.
         * 삽입 시 늘어난 MBR 영역을 강조하여 그림.
         */
        private void drawExpandedMBR(Graphics2D g, double scale, int yOffset) {
            int x = (int) (lastExpandedMbr.getLeftTop().getX() * scale) + PADDING;
            int y = yOffset - (int) (lastExpandedMbr.getRightBottom().getY() * scale);
            int w = (int) ((lastExpandedMbr.getRightBottom().getX() - lastExpandedMbr.getLeftTop().getX()) * scale);
            int h = (int) ((lastExpandedMbr.getRightBottom().getY() - lastExpandedMbr.getLeftTop().getY()) * scale);

            g.setColor(new Color(255, 200, 0));
            g.setStroke(new BasicStroke(3));
            g.drawRect(x, y, w, h);
            g.setStroke(new BasicStroke(1));
        }

        /**
         * 모든 점 그리기 메서드.
         * 트리에 저장된 모든 포인트를 화면에 점으로 그림.
         */
        private void drawAllPoints(Graphics2D g, Node node, double scale, int yOffset) {
            if (node == null) return;

            if (node.leaf && node.points != null) {
                for (Point p : node.points) {
                    int px = (int) (p.getX() * scale) + PADDING;
                    int py = yOffset - (int) (p.getY() * scale);
                    g.setColor(Color.BLACK);
                    g.fillOval(px - 2, py - 2, 4, 4);
                }
            } else if (node.children != null) {
                for (Node child : node.children) {
                    drawAllPoints(g, child, scale, yOffset);
                }
            }
        }

        /**
         * 강조 점 그리기 메서드.
         * 검색 결과나 KNN 결과로 선택된 점들을 강조하여 그림.
         */
        private void drawHighlightedPoints(Graphics2D g, double scale, int yOffset) {
            List<Point> points = new ArrayList<>(highlightedPoints);
            g.setFont(new Font("SansSerif", Font.BOLD, 11));

            if (currentSearchRect != null) {
                for (Point p : points) {
                    int x = (int) (p.getX() * scale) + PADDING;
                    int y = yOffset - (int) (p.getY() * scale);
                    g.setColor(new Color(255, 0, 0));
                    g.fillOval(x - 5, y - 5, 10, 10);
                    g.setColor(Color.BLACK);
                    g.setStroke(new BasicStroke(2));
                    g.drawOval(x - 5, y - 5, 10, 10);
                    g.setStroke(new BasicStroke(1));
                }
            }
            else if (currentKnnSource != null) {
                int idx = 1;
                for (Point p : points) {
                    int x = (int) (p.getX() * scale) + PADDING;
                    int y = yOffset - (int) (p.getY() * scale);

                    g.setColor(new Color(0, 100, 255));
                    g.fillOval(x - 7, y - 7, 14, 14);
                    g.setColor(Color.WHITE);
                    g.setFont(new Font("SansSerif", Font.BOLD, 12));
                    String label = String.valueOf(idx++);
                    int labelWidth = g.getFontMetrics().stringWidth(label);
                    g.drawString(label, x - labelWidth/2, y + 4);

                    Double dist = knnResultDistances.get(p);
                    if (dist != null) {
                        g.setColor(Color.BLACK);
                        g.setFont(new Font("SansSerif", Font.PLAIN, 10));
                        g.drawString(String.format("%.2f", dist), x + 10, y + 15);
                    }
                }
            }
        }

        /**
         * 신규 점 그리기 메서드.
         * 방금 삽입된 점을 강조 효과와 함께 그림.
         */
        private void drawNewPoint(Graphics2D g, double scale, int yOffset) {
            int x = (int) (lastInsertedPoint.getX() * scale) + PADDING;
            int y = yOffset - (int) (lastInsertedPoint.getY() * scale);

            g.setColor(new Color(0, 255, 0, 100));
            g.fillOval(x - 12, y - 12, 24, 24);
            g.setColor(new Color(0, 255, 0));
            g.fillOval(x - 5, y - 5, 10, 10);
            g.setColor(Color.BLACK);
            g.setStroke(new BasicStroke(2));
            g.drawOval(x - 5, y - 5, 10, 10);
            g.setStroke(new BasicStroke(1));
        }

        /**
         * 삭제 점 그리기 메서드.
         * 삭제 중인 점을 빨간 X표시로 그림.
         */
        private void drawDeletingPoint(Graphics2D g, double scale, int yOffset) {
            int x = (int) (deletingPoint.getX() * scale) + PADDING;
            int y = yOffset - (int) (deletingPoint.getY() * scale);

            g.setColor(new Color(255, 0, 0));
            g.setStroke(new BasicStroke(3));
            g.drawLine(x - 7, y - 7, x + 7, y + 7);
            g.drawLine(x + 7, y - 7, x - 7, y + 7);
            g.setStroke(new BasicStroke(1));
        }
    }

    /**
     * 거리-객체 쌍 클래스.
     * KNN 탐색 시 우선순위 큐에서 거리와 객체(Node 또는 Point)를 함께 관리함.
     */
    private class DistSpat implements Comparable<DistSpat> {
        final double dist;
        final Object item;
        DistSpat(Object item, double dist) { this.item = item; this.dist = dist; }
        @Override public int compareTo(DistSpat other) { return Double.compare(this.dist, other.dist); }
    }

    /**
     * RTreeImpl 생성자.
     * GUI 창을 초기화하고 화면에 띄움.
     */
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

    /**
     * GUI 갱신 메서드.
     * EDT(Event Dispatch Thread)에서 repaint()를 호출하여 화면을 다시 그림.
     */
    private void updateGUI() {
        if (this.guiPanel != null) {
            SwingUtilities.invokeLater(() -> {
                guiPanel.repaint();
            });
        }
    }

    /**
     * 점 삽입 메서드.
     * 점을 입력받아 적절한 리프 노드를 찾고 삽입하며, 필요 시 노드를 분할하고 GUI를 갱신함.
     */
    @Override
    public void add(Point point) {
        this.currentSearchRect = null;
        this.currentKnnSource = null;
        this.highlightedPoints.clear();
        this.prunedNodes.clear();
        this.knnVisitedNodes.clear();
        this.splitGroup1 = null;
        this.splitGroup2 = null;
        this.deletingPoint = null;
        this.shrinkingMbr = null;

        if (findLeaf(root, point) != null) {
            return;
        }

        Node leaf = chooseLeaf(root, point);

        if (leaf.hasValidMbr()) {
            this.lastExpandedMbr = new Rectangle(leaf.mbr.getLeftTop(), leaf.mbr.getRightBottom());
        }

        this.lastInsertedPoint = point;

        insert(leaf, point);
        this.size++;
        updateGUI();

        try {
            Thread.sleep(1500);
        } catch (InterruptedException e) {
            e.printStackTrace();
        }

        this.lastInsertedPoint = null;
        this.lastExpandedMbr = null;
        this.splitGroup1 = null;
        this.splitGroup2 = null;
        updateGUI();
    }

    /**
     * 범위 검색 메서드.
     * 지정된 사각형 영역 내의 점들을 탐색하여 반환함. Task 완료 알림을 포함.
     */
    @Override
    public Iterator<Point> search(Rectangle rectangle) {
        JOptionPane.showMessageDialog(guiFrame,
                "Task 1 complete\n\nPress OK to start Range Search...",
                "Task 1 Complete", JOptionPane.INFORMATION_MESSAGE);

        this.currentSearchRect = null;
        this.currentKnnSource = null;
        this.highlightedPoints.clear();
        this.prunedNodes.clear();
        this.knnVisitedNodes.clear();
        this.knnCandidatePoints.clear();
        this.lastInsertedPoint = null;
        this.lastExpandedMbr = null;
        this.splitGroup1 = null;
        this.splitGroup2 = null;

        List<Point> result = new ArrayList<>();
        this.currentSearchRect = rectangle;
        this.highlightedPoints.clear();
        this.prunedNodes.clear();

        updateGUI();
        try { Thread.sleep(800); } catch (InterruptedException e) {}

        searchRecursiveWithPruning(root, rectangle, result);

        this.highlightedPoints.addAll(result);
        updateGUI();
        try { Thread.sleep(1000); } catch (InterruptedException e) {}

        JOptionPane.showMessageDialog(guiFrame,
                "Task 2 complete\n\nFound " + result.size() + " points\n\nPress OK to continue...",
                "Task 2 Complete", JOptionPane.INFORMATION_MESSAGE);

        return result.iterator();
    }

    /**
     * 재귀 검색 헬퍼 메서드.
     * 노드의 MBR이 검색 영역과 겹치는지 확인하여 가지치기(Pruning)를 수행하며 탐색함.
     */
    private void searchRecursiveWithPruning(Node node, Rectangle rectangle, List<Point> result) {
        if (node.leaf) {
            for (Point p : node.points) {
                if (rectContains(rectangle, p)) {
                    result.add(p);
                    this.highlightedPoints.clear();
                    this.highlightedPoints.addAll(result);
                    updateGUI();
                    try { Thread.sleep(400); } catch (InterruptedException e) {}
                }
            }
        } else {
            for (Node child : node.children) {
                if (rectIntersects(child.getMbr(), rectangle)) {
                    searchRecursiveWithPruning(child, rectangle, result);
                } else {
                    prunedNodes.add(child);
                    collectAllDescendants(child, prunedNodes);
                    updateGUI();
                    try { Thread.sleep(500); } catch (InterruptedException e) {}
                }
            }
        }
    }

    /**
     * 자손 노드 수집 헬퍼 메서드.
     * 가지치기된 노드의 시각화를 위해 모든 하위 노드를 수집함.
     */
    private void collectAllDescendants(Node node, List<Node> list) {
        if (!node.leaf && node.children != null) {
            for (Node child : node.children) {
                list.add(child);
                collectAllDescendants(child, list);
            }
        }
    }

    /**
     * KNN 검색 메서드.
     * 주어진 점(source)에서 가장 가까운 k개의 점을 탐색하여 반환함. 우선순위 큐를 사용한 Best-First 탐색 수행.
     */
    @Override
    public Iterator<Point> nearest(Point source, int maxCount) {
        JOptionPane.showMessageDialog(guiFrame,
                "Task 2 complete\n\nPress OK to start KNN search...",
                "Task 2 Complete", JOptionPane.INFORMATION_MESSAGE);

        this.currentSearchRect = null;
        this.prunedNodes.clear();
        this.knnVisitedNodes.clear();
        this.knnVisitOrder.clear();
        this.knnCandidatePoints.clear();
        this.knnResultDistances.clear();
        this.knnNewlyFoundPoint = null;
        this.knnCurrentNode = null;
        this.highlightedPoints.clear();
        this.lastInsertedPoint = null;
        this.lastExpandedMbr = null;
        this.splitGroup1 = null;
        this.splitGroup2 = null;
        this.knnCurrentBestDist = Double.POSITIVE_INFINITY;
        this.currentKnnSource = source;

        PriorityQueue<DistSpat> pq = new PriorityQueue<>();
        pq.add(new DistSpat(root, 0.0));
        List<Point> result = new ArrayList<>();
        int visitOrder = 1;

        while (!pq.isEmpty() && result.size() < maxCount) {
            DistSpat current = pq.poll();

            if (current.item instanceof Point) {
                Point p = (Point) current.item;
                result.add(p);
                double dist = source.distance(p);

                this.knnNewlyFoundPoint = p;
                this.knnCandidatePoints.remove(p);
                updateGUI();
                try { Thread.sleep(1000); } catch (InterruptedException e) {}

                this.knnCurrentBestDist = dist;
                this.knnResultDistances.put(p, dist);
                this.knnNewlyFoundPoint = null;

                this.highlightedPoints.clear();
                this.highlightedPoints.addAll(result);
                updateGUI();
                try { Thread.sleep(800); } catch (InterruptedException e) {}

            } else {
                Node node = (Node) current.item;
                this.knnCurrentNode = node;
                knnVisitedNodes.add(node);
                knnVisitOrder.put(node, visitOrder++);
                updateGUI();
                try { Thread.sleep(700); } catch (InterruptedException e) {}

                if (node.leaf) {
                    for (Point p : node.points) {
                        this.knnCandidatePoints.add(p);
                        pq.add(new DistSpat(p, rectMinDistance(new Rectangle(p,p), source)));
                    }
                    updateGUI();
                    try { Thread.sleep(600); } catch (InterruptedException e) {}
                } else {
                    for (Node child : node.children) {
                        if (child.hasValidMbr()) {
                            double minDist = rectMinDistance(child.getMbr(), source);
                            if (result.size() == maxCount && minDist > knnCurrentBestDist) {
                                prunedNodes.add(child);
                                collectAllDescendants(child, prunedNodes);
                                updateGUI();
                                try { Thread.sleep(500); } catch (InterruptedException e) {}
                            } else {
                                pq.add(new DistSpat(child, minDist));
                            }
                        }
                    }
                }

                this.knnCurrentNode = null;
            }
        }

        this.knnVisitedNodes.clear();
        this.knnVisitOrder.clear();
        this.knnCandidatePoints.clear();
        this.prunedNodes.clear();
        this.highlightedPoints.clear();
        this.highlightedPoints.addAll(result);
        updateGUI();
        try { Thread.sleep(1000); } catch (InterruptedException e) {}

        JOptionPane.showMessageDialog(guiFrame,
                "Task 3 complete\n\nFound " + result.size() + " nearest points\n\nPress OK to continue...",
                "Task 3 Complete", JOptionPane.INFORMATION_MESSAGE);

        return result.iterator();
    }

    /**
     * 점 삭제 메서드.
     * 지정된 점을 찾아 트리에서 제거하고, 언더플로우 발생 시 트리를 재조정(Condense)함.
     */
    @Override
    public void delete(Point point) {
        if (firstDeleteCall) {
            firstDeleteCall = false;

            JOptionPane.showMessageDialog(guiFrame,
                    "Task 3 complete\n\nPress OK to start deletion...",
                    "Task 3 Complete", JOptionPane.INFORMATION_MESSAGE);

            this.currentSearchRect = null;
            this.currentKnnSource = null;
            this.highlightedPoints.clear();
            this.prunedNodes.clear();
            this.knnVisitedNodes.clear();
            this.knnVisitOrder.clear();
            this.knnCandidatePoints.clear();
            this.lastInsertedPoint = null;
            this.lastExpandedMbr = null;
            this.splitGroup1 = null;
            this.splitGroup2 = null;
            updateGUI();
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

        this.deletingPoint = point;
        this.deletingLeafNode = leaf;
        updateGUI();
        try { Thread.sleep(600); } catch (InterruptedException e) {}

        this.oldMbrBeforeDelete = new Rectangle(leaf.mbr.getLeftTop(), leaf.mbr.getRightBottom());

        leaf.points.remove(toRemove);
        leaf.recalcMbr();

        if (leaf.hasValidMbr()) {
            this.shrinkingMbr = new Rectangle(leaf.mbr.getLeftTop(), leaf.mbr.getRightBottom());
        }
        this.deletingPoint = null;
        updateGUI();
        try { Thread.sleep(700); } catch (InterruptedException e) {}

        condenseTree(leaf);
        this.size--;

        if (size == 0) {
            root = new Node(true, null);
        }

        this.deletingLeafNode = null;
        this.shrinkingMbr = null;
        this.oldMbrBeforeDelete = null;
        updateGUI();
    }

    /**
     * 트리 비움 확인 메서드.
     * 트리에 저장된 점이 없는지 여부를 반환함.
     */
    @Override
    public boolean isEmpty() {
        updateGUI();
        boolean result = (this.size == 0);

        JOptionPane.showMessageDialog(guiFrame,
                "Task 4 complete" ,
                "Task 4 complete", JOptionPane.INFORMATION_MESSAGE);

        return result;
    }

    /**
     * 리프 노드 선택 메서드.
     * 점을 삽입할 때 면적 증가량이 가장 적은 리프 노드를 선택하여 반환함.
     */
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

    /**
     * 삽입 실행 메서드.
     * 리프 노드에 점을 추가하고, 오버플로우 발생 시 노드를 분할(Split)함.
     */
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

    /**
     * 노드 분할 메서드.
     * Quadratic Split 알고리즘을 사용하여 노드를 두 개의 그룹으로 분할함.
     */
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

        group1.recalcMbr();
        group2.recalcMbr();

        entries.remove(seed1);
        entries.remove(seed2);

        while (!entries.isEmpty()) {
            if (group1.leaf) {
                if (group1.points.size() + entries.size() == MIN_ENTRIES) {
                    for (Object e : new ArrayList<>(entries)) {
                        group1.points.add((Point) e);
                    }
                    entries.clear();
                    break;
                }
                if (group2.points.size() + entries.size() == MIN_ENTRIES) {
                    for (Object e : new ArrayList<>(entries)) {
                        group2.points.add((Point) e);
                    }
                    entries.clear();
                    break;
                }
            } else {
                if (group1.children.size() + entries.size() == MIN_ENTRIES) {
                    for (Object e : new ArrayList<>(entries)) {
                        group1.children.add((Node) e);
                        ((Node)e).parent = group1;
                    }
                    entries.clear();
                    break;
                }
                if (group2.children.size() + entries.size() == MIN_ENTRIES) {
                    for (Object e : new ArrayList<>(entries)) {
                        group2.children.add((Node) e);
                        ((Node)e).parent = group2;
                    }
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

        this.splitGroup1 = group1;
        this.splitGroup2 = group2;
        updateGUI();
        try { Thread.sleep(1000); } catch (InterruptedException e) {}

        return new Node[] { group1, group2 };
    }

    /**
     * 시드 선택 헬퍼 메서드.
     * 분할 시 가장 비효율적인(낭비 면적이 큰) 두 엔트리를 초기 시드로 선택함.
     */
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

    /**
     * 다음 엔트리 선택 헬퍼 메서드.
     * 두 그룹 간의 면적 증가량 차이가 가장 큰 엔트리를 선택함.
     */
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

    /**
     * 트리 조정 메서드.
     * 삽입 또는 분할 후 부모 노드로 거슬러 올라가며 MBR을 갱신하고 분할을 전파함.
     */
    private void adjustTree(Node node, Node newNode) {
        Node n = node;
        Node nn = newNode;
        while (n != root) {
            Node parent = n.parent;
            if (parent == null) break;

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

        if (nn != null) {
            Node newRoot = new Node(false, null);
            newRoot.children.add(n);
            newRoot.children.add(nn);
            n.parent = newRoot;
            nn.parent = newRoot;
            newRoot.recalcMbr();
            this.root = newRoot;
        } else {
            root.recalcMbr();
        }
    }

    /**
     * 재귀 검색 헬퍼 메서드 (미사용).
     * 단순 포함 여부 확인을 통한 검색 (searchRecursiveWithPruning이 대신 사용됨).
     */
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

    /**
     * 리프 검색 메서드.
     * 특정 점을 포함하고 있는 리프 노드를 찾아 반환함.
     */
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

    /**
     * 트리 압축 메서드.
     * 삭제 후 언더플로우가 발생한 노드들을 처리하고 MBR을 갱신하며 루트까지 올라감.
     */
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

            if(parent.children.contains(n)) {
                n = parent;
            } else {
                n = parent;
            }
        }

        if (!root.leaf && root.children.size() == 1) {
            Node oldRoot = root;
            root = root.children.get(0);
            root.parent = null;
            oldRoot.children.clear();
        }
    }

    /**
     * 언더플로우 처리 메서드.
     * 엔트리 수가 부족한 노드를 형제 노드와 병합하거나 재분배함.
     */
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

        if (node.leaf) {
            if (sibling.points.size() + node.points.size() <= MAX_ENTRIES) {
                sibling.points.addAll(node.points);
                parent.children.remove(node);
                node.points.clear();
                sibling.recalcMbr();
            } else {
                while (node.points.size() < MIN_ENTRIES && sibling.points.size() > MIN_ENTRIES) {
                    Point borrow = sibling.points.remove(sibling.points.size() - 1);
                    node.points.add(0, borrow);
                }
                node.recalcMbr();
                sibling.recalcMbr();
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
                while (node.children.size() < MIN_ENTRIES && sibling.children.size() > MIN_ENTRIES) {
                    Node borrow = sibling.children.remove(sibling.children.size() - 1);
                    borrow.parent = node;
                    node.children.add(0, borrow);
                }
                node.recalcMbr();
                sibling.recalcMbr();
            }
        }
    }

    /**
     * 무효 MBR 생성 메서드.
     * 초기화나 빈 상태를 나타내는 무효한(무한대 좌표) 사각형을 생성함.
     */
    private Rectangle createInvalidMbr() {
        return new Rectangle(
                new Point(Double.POSITIVE_INFINITY, Double.POSITIVE_INFINITY),
                new Point(Double.NEGATIVE_INFINITY, Double.NEGATIVE_INFINITY));
    }

    /**
     * 면적 계산 메서드.
     * 사각형의 너비와 높이를 곱하여 면적을 반환함.
     */
    private double rectArea(Rectangle r) {
        if (r.getLeftTop().getX() == Double.POSITIVE_INFINITY) {
            return 0;
        }
        double width = r.getRightBottom().getX() - r.getLeftTop().getX();
        double height = r.getRightBottom().getY() - r.getLeftTop().getY();
        return width * height;
    }

    /**
     * 포함 여부 확인 메서드.
     * 사각형이 특정 점을 내부에 포함하는지 여부를 반환함.
     */
    private boolean rectContains(Rectangle r, Point p) {
        if (r == null || p == null || r.getLeftTop().getX() == Double.POSITIVE_INFINITY) {
            return false;
        }
        return p.getX() >= r.getLeftTop().getX() &&
                p.getX() <= r.getRightBottom().getX() &&
                p.getY() >= r.getLeftTop().getY() &&
                p.getY() <= r.getRightBottom().getY();
    }

    /**
     * 교차 여부 확인 메서드.
     * 두 사각형이 서로 겹치는지 여부를 반환함.
     */
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

    /**
     * 면적 증가량 계산 메서드.
     * 점을 포함하기 위해 확장했을 때 늘어나는 면적의 양을 반환함.
     */
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

    /**
     * 면적 증가량 계산 메서드 (Overloaded).
     * 다른 사각형을 포함하기 위해 확장했을 때 늘어나는 면적의 양을 반환함.
     */
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

    /**
     * 병합 메서드.
     * 두 사각형을 모두 포함하는 최소 경계 사각형(MBR)을 생성하여 반환함.
     */
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

    /**
     * 최소 거리 계산 메서드.
     * 사각형과 점 사이의 최단 유클리드 거리를 반환함 (MINDIST).
     */
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
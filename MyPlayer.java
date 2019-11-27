
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.PriorityQueue;
import java.util.Random;
import java.util.Set;
import java.util.stream.Collectors;

/*
 *
 * @author shrey
 */
public class MyPlayer implements PokerSquaresPlayer {

    private final int SIZE = 5;
    private final int NUM_POS = SIZE * SIZE;
    private final int NUM_CARDS = Card.NUM_CARDS;
    private Random random = new Random();
    private int[] plays = new int[NUM_POS];
    private int numPlays = 0;
    private PokerSquaresPointSystem system;
    private Card[][] grid = new Card[SIZE][SIZE];
    private Card[] simDeck = Card.getAllCards();
    private int[] rankMap = new int[Card.NUM_RANKS];
    private int[] suitMap = new int[Card.NUM_SUITS];
    private List<Set<Integer>> straights = new LinkedList<>();

    private Set<Integer> availablePositions = new HashSet<>();

    @Override
    public void setPointSystem(PokerSquaresPointSystem system, long millis) {
        this.system = system;
    }

    @Override
    public void init() {
        simDeck = Card.getAllCards();
        // clear grid
        for (int row = 0; row < SIZE; row++) {
            for (int col = 0; col < SIZE; col++) {
                grid[row][col] = null;
            }
        }
        // reset numPlays
        numPlays = 0;
        // (re)initialize list of play positions (row-major ordering)
        for (int i = 0; i < NUM_POS; i++) {
            plays[i] = i;
            availablePositions.add(i);
        }

        for (int i = 0; i < Card.NUM_RANKS; i++) {
            rankMap[i] = 4;
            if (i < Card.NUM_RANKS - 3) {
                Set<Integer> straight = new HashSet<>();

                if (i == 9) {
                    for (int j = i; j < i + 4; j++) {
                        straight.add(j);
                    }
                    straight.add(0);
                } else {
                    for (int j = i; j < i + 5; j++) {
                        straight.add(j);
                    }
                }
                straights.add(straight);
            }
        }

        for (int i = 0; i < Card.NUM_SUITS; i++) {
            suitMap[i] = 13;
        }

    }

    @Override
    public int[] getPlay(Card card, long millisRemaining) {
        long starttime = System.currentTimeMillis();
        int rowColPosition = 0, row = 0, col = 0, rowEmptyCount, colEmptyCount;
        rankMap[card.getRank()]--;
        suitMap[card.getSuit()]--;
        simDeck[card.getCardId()] = null;
        List<Integer> bestPlays = new ArrayList<>();

        switch (numPlays) {
            case 0:
                rowColPosition = random.nextInt(NUM_POS);
                break;
            case NUM_POS - 1:
                rowColPosition = availablePositions.iterator().next();
                break;
            default:
                int maxPoints = Integer.MIN_VALUE;
                PriorityQueue<Position> pq = new PriorityQueue(new PositionComparator());
                for (int pos : availablePositions) {
                    rowEmptyCount = 0;
                    colEmptyCount = 0;
                    row = pos / SIZE;
                    col = pos % SIZE;
                    grid[row][col] = card;
                    Card[] rowCheck = new Card[5];
                    Card[] colCheck = new Card[5];
                    for (int j = 0; j < 5; j++) {
                        if (grid[row][j] == null) {
                            rowEmptyCount++;
                        }
                        if (grid[j][col] == null) {
                            colEmptyCount++;
                        }
                        rowCheck[j] = grid[row][j];
                        colCheck[j] = grid[j][col];

                    }

                    int basePoints = 0;
                    int rowPoints = system.getHandScore(rowCheck);
                    basePoints += rowPoints;
                    rowPoints += (rowEmptyCount > 0) ? checkPoints(rowCheck, rowEmptyCount, rowPoints) : 0;
                    int colPoints = system.getHandScore(colCheck);
                    basePoints += colPoints;
                    colPoints += (colEmptyCount > 0) ? checkPoints(colCheck, colEmptyCount, colPoints) : 0;

                    pq.add(new Position(pos, basePoints, rowPoints + colPoints, rowEmptyCount + colEmptyCount));

                    grid[row][col] = null;
                }

                // Simulation part
                long timeRemaining = millisRemaining - (System.currentTimeMillis() - starttime);
                long millisPerPlay = timeRemaining / (NUM_POS - numPlays - 1);
                long millisPerPosition = millisPerPlay / 5;
                long simEndTime;
                int simPlay = pq.size() > 5 ? 5 : pq.size();
                int totalPoints,
                 totalSims;
                Set<Integer> greedyAvailablePositions;

                while (simPlay > 0) {
                    totalPoints = 0;
                    totalSims = 0;
                    int priorityPos = pq.poll().getPosition();
                    greedyAvailablePositions = new HashSet<>(availablePositions);
                    greedyAvailablePositions.remove(priorityPos);
                    grid[priorityPos / SIZE][priorityPos % SIZE] = card;
                    int basePoints = system.getScore(grid);
                    simEndTime = System.currentTimeMillis() + millisPerPosition;
                    while (System.currentTimeMillis() < simEndTime) {
                        totalPoints += simGreedyPlay(priorityPos, greedyAvailablePositions);
                        totalSims++;
                    }

                    //undoing
                    grid[priorityPos / SIZE][priorityPos % SIZE] = card;

                    int averageScore = totalPoints / totalSims;

                    if (averageScore > maxPoints) {
                        maxPoints = basePoints + averageScore;
                        bestPlays.clear();
                        bestPlays.add(priorityPos);
                    } else if (averageScore == maxPoints) {
                        bestPlays.add(priorityPos);
                    }

                    simPlay--;
                }

                rowColPosition = bestPlays.get(random.nextInt(bestPlays.size()));
                break;
        }

        availablePositions.remove(rowColPosition);
        numPlays++;
        int[] playPos = {rowColPosition / SIZE, rowColPosition % SIZE};
        grid[playPos[0]][playPos[1]] = card;

        return playPos;
    }

    @Override
    public String getName() {
        return "MyPlayer";
    }

    public int checkPoints(Card[] list, int emptyCount, int basePoints) {
        Set<Integer> ranks = new HashSet<>();
        Set<Integer> suits = new HashSet<>();
        Map<Integer, Long> rankCount = Arrays.asList(list).stream().filter(c -> c != null).
                collect(Collectors.groupingBy(Card -> Card.getRank(), Collectors.counting()));
        int minRank = Integer.MAX_VALUE;
        for (Card c : list) {
            if (c == null) {
                continue;
            }
            ranks.add(c.getRank());
            suits.add(c.getSuit());
            if (c.getRank() != 0 && c.getRank() < minRank) {
                minRank = c.getRank();
            }
        }

        int possiblePoints = 0;
        int hands = 0;

        if (basePoints == system.getHandScore(PokerHand.HIGH_CARD)) {
            possiblePoints += system.getHandScore(PokerHand.ONE_PAIR);
            hands += 1;
            switch (emptyCount) {
                case 4:
                    possiblePoints += system.getHandScore(PokerHand.TWO_PAIR);
                    possiblePoints += system.getHandScore(PokerHand.THREE_OF_A_KIND);
                    possiblePoints += system.getHandScore(PokerHand.FOUR_OF_A_KIND);
                    possiblePoints += system.getHandScore(PokerHand.FULL_HOUSE);
                    hands += 4;
                    break;
                case 3:
                    possiblePoints += system.getHandScore(PokerHand.TWO_PAIR);
                    possiblePoints += system.getHandScore(PokerHand.THREE_OF_A_KIND);
                    hands += 2;
                    for (int r : ranks) {
                        if (rankMap[r] > 1) {
                            possiblePoints += system.getHandScore(PokerHand.FULL_HOUSE);
                            hands += 1;
                            break;
                        }
                    }
                    break;
                case 2:
                    int pairsPossible = 0,
                     triplets = 0;
                    for (int r : ranks) {
                        if (rankMap[r] == 1) {
                            pairsPossible++;
                        } else if (rankMap[r] == 2) {
                            triplets++;
                        }
                    }
                    if (pairsPossible == 2) {
                        possiblePoints += system.getHandScore(PokerHand.TWO_PAIR);
                        hands += 1;
                    }
                    if (triplets > 0) {
                        possiblePoints += system.getHandScore(PokerHand.THREE_OF_A_KIND);
                        hands += 1;
                    }
                    break;
                default:
                    break;
            }

        } else if (basePoints == system.getHandScore(PokerHand.ONE_PAIR)) {
            switch (emptyCount) {
                case 3:
                    possiblePoints += system.getHandScore(PokerHand.FULL_HOUSE);
                    possiblePoints += system.getHandScore(PokerHand.TWO_PAIR);
                    hands += 2;
                    if (rankMap[ranks.iterator().next()] == 2) {
                        possiblePoints += system.getHandScore(PokerHand.FOUR_OF_A_KIND);
                        hands += 1;
                    } else if (rankMap[ranks.iterator().next()] == 1) {
                        possiblePoints += system.getHandScore(PokerHand.THREE_OF_A_KIND);
                        hands += 1;
                    }
                    break;
                case 2: {
                    possiblePoints += system.getHandScore(PokerHand.TWO_PAIR);
                    hands += 1;
                    int pairElement = 0, singleElement = 0;
                    for (Map.Entry<Integer, Long> entry : rankCount.entrySet()) {
                        if (entry.getValue() == 2) {
                            pairElement = entry.getKey();
                        } else {
                            singleElement = entry.getKey();
                        }
                    }
                    if (rankMap[pairElement] == 2) {
                        possiblePoints += system.getHandScore(PokerHand.FOUR_OF_A_KIND);
                        hands += 1;
                    }
                    if (rankMap[pairElement] >= 1 || rankMap[singleElement] >= 2) {
                        possiblePoints += system.getHandScore(PokerHand.THREE_OF_A_KIND);
                        possiblePoints += system.getHandScore(PokerHand.FULL_HOUSE);
                        hands += 2;
                    }
                    break;
                }
                default: {
                    int pairElement = 0;
                    for (Map.Entry<Integer, Long> entry : rankCount.entrySet()) {
                        if (entry.getValue() == 2) {
                            pairElement = entry.getKey();
                        }
                        if (rankMap[pairElement] >= 1) {
                            possiblePoints += system.getHandScore(PokerHand.THREE_OF_A_KIND);
                            hands += 1;
                        }
                        for (int r : ranks) {
                            if (r != pairElement && rankMap[r] >= 1) {
                                possiblePoints += system.getHandScore(PokerHand.TWO_PAIR);
                                hands += 1;
                                break;
                            }
                        }
                    }
                    break;
                }
            }
        } else if (basePoints == system.getHandScore(PokerHand.TWO_PAIR)) {
            for (int r : ranks) {
                if (rankMap[r] >= 1) {
                    possiblePoints += system.getHandScore(PokerHand.FULL_HOUSE);
                    hands += 1;
                }
            }

        } else if (basePoints == system.getHandScore(PokerHand.THREE_OF_A_KIND)) {
            int tripletElement = 0, singleElement = -1;
            for (Map.Entry<Integer, Long> entry : rankCount.entrySet()) {
                if (entry.getValue() == 3) {
                    tripletElement = entry.getKey();
                } else {
                    singleElement = entry.getKey();
                }

            }

            if (rankMap[tripletElement] == 1) {
                possiblePoints += system.getHandScore(PokerHand.FOUR_OF_A_KIND);
                hands += 1;
            }
            if ((singleElement != -1 && rankMap[singleElement] >= 1) || emptyCount == 2) {
                possiblePoints += system.getHandScore(PokerHand.FULL_HOUSE);
                hands += 1;
            }

        }

        if (suits.size() == 1) {

            // then 1st check flush possible
            if (suitMap[suits.iterator().next()] >= emptyCount) {
                possiblePoints += system.getHandScore(PokerHand.FLUSH);
                hands += 1;

                if (checkStraight(suits, true, ranks)) {
                    possiblePoints += system.getHandScore(PokerHand.STRAIGHT_FLUSH);
                    hands += 1;
                }
            }

            // then check royal flush possible
            if (minRank >= 9 && checkRoyalFlush(suits.iterator().next(), ranks)) {
                possiblePoints += system.getHandScore(PokerHand.ROYAL_FLUSH);
                hands += 1;
            }
        }

        if (checkStraight(suits, false, ranks)) {
            possiblePoints += system.getHandScore(PokerHand.STRAIGHT);
            hands += 1;
        }

        return hands != 0 ? possiblePoints / hands : 0;
    }

    public boolean checkStraight(Set<Integer> suits, boolean isFlush, Set<Integer> ranks) {
        Set<Integer> temp;
        for (Set<Integer> straight : straights) {
            if (straight.containsAll(ranks)) {
                temp = new HashSet<>(straight);
                temp.removeAll(ranks);
                if (isFlush) {
                    int suit = suits.iterator().next();
                    for (Integer i : temp) {
                        if (simDeck[(suit * Card.NUM_RANKS) + i] == null) {
                            return false;
                        }
                    }
                    return true;
                } else {
                    boolean flag = true;
                    for (Integer i : temp) {
                        if (rankMap[i] == 0) {
                            flag = false;
                        }
                    }
                    if (flag == true) {
                        return true;
                    }
                }

            }

        }
        return false;
    }

    public boolean checkRoyalFlush(int suit, Set<Integer> ranks) {
        if (!ranks.contains(0) && simDeck[(suit * Card.NUM_RANKS) + 0] == null) {
            return false;
        }
        for (int j = 9; j < 13; j++) {
            if (!ranks.contains(j) && simDeck[(suit * Card.NUM_RANKS) + j] == null) {
                return false;
            }
        }

        return true;

    }

    public int simGreedyPlay(int position, Set<Integer> availablePositions) {
        int remainingPlays = availablePositions.size(), col = 0, row = 0;
        List<Integer> bestPlays = new ArrayList<>();
        int[] undoTrack = new int[remainingPlays];
        int maxScore = Integer.MIN_VALUE;
        List<Card> deck = Arrays.asList(simDeck).stream().filter(c -> c != null).collect(Collectors.toList());
        for (int i = 0; i < remainingPlays; i++) {
            int randomIndex = random.nextInt(deck.size());
            Card card = deck.get(randomIndex);
            bestPlays.clear();
            maxScore = Integer.MIN_VALUE;
            for (int pos : availablePositions) {
                row = pos / SIZE;
                col = pos % SIZE;
                grid[row][col] = card;
                int score = system.getScore(grid);
                if (score > maxScore) {
                    maxScore = score;
                    bestPlays.clear();
                    bestPlays.add(pos);
                } else if (score == maxScore) {
                    bestPlays.add(pos);
                }

                grid[row][col] = null;
            }

            deck.remove(randomIndex);
            int checkr = random.nextInt(bestPlays.size());
            int selectedPos = bestPlays.get(checkr);
            undoTrack[i] = selectedPos;
            availablePositions.remove(selectedPos);
            grid[selectedPos / SIZE][selectedPos % SIZE] = card;

        }

        int finalScore = system.getScore(grid);

        for (int i = 0; i < remainingPlays; i++) {
            grid[undoTrack[i] / SIZE][undoTrack[i] % SIZE] = null;
        }

        return finalScore;

    }

    public static void main(String[] args) {
        PokerSquaresPointSystem system = PokerSquaresPointSystem.getBritishPointSystem();
        System.out.println(system);
        new PokerSquares(new MyPlayer(), system).play();
    }

}

class Position {

    private int position;
    private int basePoints;
    private int totalPoints;
    private int emptyCount;

    public Position(int position, int basePoints, int totalPoints, int emptyCount) {
        this.position = position;
        this.basePoints = basePoints;
        this.totalPoints = totalPoints;
        this.emptyCount = emptyCount;

    }

    public int getEmptyCount() {
        return emptyCount;
    }

    public void setEmptyCount(int emptyCount) {
        this.emptyCount = emptyCount;
    }

    public int getPosition() {
        return position;
    }

    public void setPosition(int position) {
        this.position = position;
    }

    public int getBasePoints() {
        return basePoints;
    }

    public void setBasePoints(int basePoints) {
        this.basePoints = basePoints;
    }

    public int getTotalPoints() {
        return totalPoints;
    }

    public void setTotalPoints(int totalPoints) {
        this.totalPoints = totalPoints;
    }
}

class PositionComparator implements Comparator<Position> {

    @Override
    public int compare(Position p1, Position p2) {
        if (p2.getTotalPoints() - p1.getTotalPoints() == 0) {
            if (p1.getBasePoints() - p2.getBasePoints() == 0){
            
                return new Random().nextBoolean() == true ? 1 : -1;
            }
            return p2.getBasePoints() - p1.getBasePoints();  
            }
                    
        return p2.getTotalPoints() - p1.getTotalPoints();
    }
}

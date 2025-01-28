import { Table } from "poker-ts";
import { FxnClient } from "./fxnClient.ts";
import Poker, { Action, Card } from "poker-ts/dist/facade/poker";

declare type SeatIndex = number;
declare type PublicKey = string;
declare type BetSize = number | null;
declare type RoundOfBetting = 'preflop' | 'flop' | 'turn' | 'river';
export declare type ActionHistoryEntry = [RoundOfBetting, SeatIndex, Action, BetSize];
export declare type ActionHistory = Array<ActionHistoryEntry>;

enum HandRanking {
    HIGH_CARD = 0,
    PAIR = 1,
    TWO_PAIR = 2,
    THREE_OF_A_KIND = 3,
    STRAIGHT = 4,
    FLUSH = 5,
    FULL_HOUSE = 6,
    FOUR_OF_A_KIND = 7,
    STRAIGHT_FLUSH = 8,
    ROYAL_FLUSH = 9
}

const HandRankingStr = [
    "High Card",
    "Pair",
    "Two Pair",
    "Three of a Kind",
    "Straight",
    "Flush",
    "Full House",
    "Four of a Kind",
    "Straight Flush",
    "Royal Flush"
];

interface Winner {
    seatIndex: SeatIndex,
    ranking: HandRanking,
    winnings: number
}

interface Player {
    totalChips: number;
    stack: number;
    betSize: BetSize;
}

interface ForcedBets {
    ante: BetSize,
    bigBlind: BetSize,
    smallBlind: BetSize
}

// Stuff that everyone at the table can know
export interface TableState {
    players: Array<Player>,
    emptySeats: Array<SeatIndex>,
    forcedBets: ForcedBets,
    numSeats: number,
    isHandInProgress: boolean,
    playerToActSeat: SeatIndex,
    playerToActKey: PublicKey,
    legalActions: Array<Action>,
    button: SeatIndex,
    isBettingRoundInProgress: boolean,
    areBettingRoundsCompleted: boolean,
    roundOfBetting: RoundOfBetting,
    communityCards: Array<Card>,
    winners: Array<Winner>
}

// Stuff that should be kept secret from other players
export interface PlayerState {
    holeCards: Card[],
    chips: number
}

const ANTE: BetSize = 0;
const BIG_BLIND: BetSize = 10;
const SMALL_BLIND: BetSize = 5;
const MAX_PLAYERS: number = 9; // Max of 23 set by poker-ts

export class PokerManager {
    private table: Poker
    private tableState: TableState;
    private playerStates: PlayerState[];
    private actionHistory: ActionHistory;
    private playerKeys: Map<SeatIndex, PublicKey>;
    private playerSeats: Map<PublicKey, SeatIndex>;
    public readonly TABLE_EMPTY_DELAY: number = 10 * 1000; // 30s delay
    public readonly NEW_HAND_DELAY: number = 30 * 1000; // 30s delay
    private tableEmptyTimer: NodeJS.Timeout | null = null;

    constructor(private fxnClient: FxnClient) {
        this.table = new Table({ante: ANTE, bigBlind: BIG_BLIND, smallBlind: SMALL_BLIND}, MAX_PLAYERS);
        this.tableState = this.initializeTableState();
        this.playerStates = new Array<PlayerState>(MAX_PLAYERS);
        this.actionHistory = new Array<ActionHistoryEntry>();
        this.playerKeys = new Map<SeatIndex, PublicKey>();
        this.playerSeats = new Map<PublicKey, SeatIndex>();
        this.startNewGame();
    }

    private initializeTableState(): TableState {
        return {
            players: new Array<Player>(),
            emptySeats: new Array<SeatIndex>(),
            forcedBets: {
                ante: -1,
                bigBlind: -1,
                smallBlind: -1
            },
            numSeats: -1,
            isHandInProgress: false,
            playerToActSeat: -1,
            playerToActKey: "",
            legalActions: new Array<Action>(),
            button: -1,
            isBettingRoundInProgress: false,
            areBettingRoundsCompleted: false,
            roundOfBetting: "preflop",
            communityCards: new Array<Card>(),
            winners: new Array<Winner>()
        }
    }

    private async startNewGame(): Promise<void> {
        console.log("Starting a new game.");
        this.actionHistory = new Array<[RoundOfBetting, SeatIndex, Action, BetSize]>();
        this.tableState.emptySeats = this.getEmptySeats();

        if (this.tableState.emptySeats.length > 0) {
            // We have empty seats, seat any subscribers
            
            const subscribers = await this.fxnClient.getHostSubscribers();
            subscribers.forEach((subscriberDetails) => {
                const publicKey = subscriberDetails.subscriber.toString();
                if (!this.playerSeats.get(publicKey)) {
                    const seatIndex = this.getEmptySeats().pop();
                    const buyIn = 300;
                    this.addPlayer(publicKey, seatIndex, buyIn);
                    console.log(`Seated ${publicKey} at chair ${seatIndex} with ${buyIn} chips.`);
                }
            });
        }

        if (this.getFilledSeats().length < 2) {
            // There are less than 2 players at the table, check again in X seconds
            if (this.tableEmptyTimer) {
                clearTimeout(this.tableEmptyTimer);
            }

            console.log("Not enough players, trying again in " + this.TABLE_EMPTY_DELAY + " seconds.");
            this.tableEmptyTimer = setTimeout(() => this.startNewGame(), this.TABLE_EMPTY_DELAY);
        }
        else
        {
            // We have at least 2 players and can start the game
            console.log("Starting the game.");
            this.startNewHand();
        }
    }

    private async startNewHand(): Promise<void> {
        console.log("Starting new hand.");
        this.table.startHand();
        this.updateTableState();
        this.playerKeys.forEach((publicKey) => {
            // Set hole cards and update chips
            this.updatePlayerHoleCards(publicKey);
            this.updatePlayerChips(publicKey);
        })

        this.BroadcastHand();
    }

    private async BroadcastHand(): Promise<void> {
        while (this.tableState.isHandInProgress) {
            while (this.tableState.isBettingRoundInProgress) {
                await this.BroadcastBettingRound();
                this.updateTableState();
            }

            console.log("Betting round over.");
            this.table.endBettingRound();
            this.updateTableState();

            if (this.tableState.areBettingRoundsCompleted) {
                await this.BroadcastShowdown();
            }
        }

        this.tableState.winners.forEach((winner) => {
            console.log(`Seat ${winner.seatIndex} wins ${winner.winnings} with ${HandRankingStr[winner.ranking]}!`);
        })

        console.log("Hand over! Starting next hand in 30s.");
        setTimeout(this.startNewHand, this.NEW_HAND_DELAY);
    }

    private async BroadcastBettingRound() {
        console.log("Starting betting round: " + this.tableState.roundOfBetting);

        const playerToActSeat: SeatIndex = this.table.playerToAct();
        const playerToActKey: PublicKey = this.playerKeys.get(playerToActSeat);

        const subscribers = await this.fxnClient.getSubscribers();

        // Broadcast to all subscribers
        const promises = subscribers.map(async (subscriberDetails) => {
            try {
                const publicKey = subscriberDetails.subscriber.toString();
                const seatIndex = this.playerSeats.get(publicKey);
                const recipient = subscriberDetails.subscription?.recipient;

                // Update the player state
                this.updatePlayerChips(publicKey);
                const playerState = this.playerStates[seatIndex];

                // Only broadcast if the subscriber is active
                if (recipient && subscriberDetails.status === 'active') {
                    const cards = playerState.holeCards;
                    const cardsString = `${cards[0].rank} of ${cards[0].suit} and ${cards[1].rank} of ${cards[1].suit}`;
                    console.log("Broadcasting to " + recipient + " cards: " + cardsString);

                    if (publicKey == playerToActKey) {
                        console.log(`Prompting ${playerToActKey} for action`);
                        
                        // Await their response
                        const response = await this.fxnClient.broadcastToSubscriber({
                            tableState: this.tableState,
                            playerState: playerState,
                            actionHistory: this.actionHistory
                        }, subscriberDetails);
                        console.log(response);

                        let action: Action = "fold";
                        let betSize = 0;
                        if (response.status == 200) {
                            // Parse their chosen action
                            const responseData = await response.json();
                            console.log(responseData);
                            action = responseData.action;
                            betSize = responseData.betSize;

                            // TODO: Validate
                        }

                        // Send the action to the table
                        console.log("Seat: " + seatIndex + " Action: " + action + " Bet: " + betSize);
                        this.table.actionTaken(action, betSize ? betSize : null);

                        // Add it to the history
                        const bettingRound = this.tableState.roundOfBetting;
                        this.actionHistory.push([bettingRound, seatIndex, action, betSize]);
                    } else {
                        // It is not this player's turn

                        // Give them their update
                        this.fxnClient.broadcastToSubscriber({
                            tableState: this.tableState,
                            playerState: playerState,
                            actionHistory: this.actionHistory
                        }, subscriberDetails);
                    }
                }
            } catch (error) {
                console.error(`Error communicating with subscriber:`, error);
            }
        });

        await Promise.all(promises);
    }

    private async BroadcastShowdown() {
        console.log("Starting showdown.");

        // If there is only one pot with one eligible player, they won't show up in winners() so add them here
        const pots = this.table.pots();
        if (pots.length == 1 && pots[0].eligiblePlayers.length == 1) {
            const seatIndex = pots[0].eligiblePlayers[0];
            const winnings = pots[0].size;
            const winnerHand = this.playerStates[seatIndex].holeCards.concat(this.table.communityCards());
            this.tableState.winners.push({
                seatIndex: seatIndex,
                ranking: this.getHandRanking(winnerHand),
                winnings: winnings
            });
        }

        this.table.showdown();
        
        if (this.table.winners().length != 0) {
            this.table.winners().forEach((pot, potIndex) => {
                pot.forEach((winner) => {
                    const seatIndex = winner[0];
                    const winnings = pots[potIndex].size;
                    const winnerHandRanking = winner[1].ranking;
                    this.tableState.winners.push({
                        seatIndex: seatIndex,
                        ranking: winnerHandRanking,
                        winnings: winnings
                    });
                })
            })
        }
        this.updateTableState();

        const subscribers = await this.fxnClient.getSubscribers();

        // Broadcast to all subscribers
        const promises = subscribers.map(async (subscriberDetails) => {
            try {
                const publicKey = subscriberDetails.subscriber.toString();
                const seatIndex = this.playerSeats.get(publicKey);
                const recipient = subscriberDetails.subscription?.recipient;
                const playerState = this.playerStates[seatIndex];

                // Only broadcast if the subscriber is active
                if (recipient && subscriberDetails.status === 'active') {
                    this.fxnClient.broadcastToSubscriber({
                        tableState: this.tableState,
                        playerState: playerState,
                        actionHistory: this.actionHistory
                    }, subscriberDetails);
                }
            } catch (error) {
                console.error(`Error communicating with subscriber:`, error);
            }
        });

        return Promise.all(promises);
    }

    private updatePlayerHoleCards(publicKey: PublicKey) {
        const seatIndex = this.playerSeats.get(publicKey);
        this.playerStates[seatIndex].holeCards = this.table.holeCards()[seatIndex];
    }

    private updatePlayerChips(publicKey: PublicKey) {
        const seatIndex = this.playerSeats.get(publicKey);
        this.playerStates[seatIndex].chips = this.table.seats()[seatIndex].stack;
    }

    private updateTableState() {
        const handinProgress = this.table.isHandInProgress();
        const bettingRoundInProgress = handinProgress ? this.table.isBettingRoundInProgress() : false;

        this.tableState.players = this.table.seats();
        this.tableState.numSeats = this.table.numSeats();
        this.tableState.emptySeats = this.getEmptySeats();
        this.tableState.forcedBets = this.table.forcedBets();

        this.tableState.isHandInProgress = handinProgress;

        this.tableState.playerToActSeat = bettingRoundInProgress ? this.table.playerToAct() : null;
        this.tableState.playerToActKey = bettingRoundInProgress ? this.playerKeys.get(this.tableState.playerToActSeat) : null;
        this.tableState.legalActions = bettingRoundInProgress ? this.table.legalActions().actions : null,
        this.tableState.button = handinProgress ? this.table.button() : null;
        this.tableState.isBettingRoundInProgress = handinProgress ? this.table.isBettingRoundInProgress() : null;
        this.tableState.roundOfBetting = handinProgress ? this.table.roundOfBetting() : null;
        this.tableState.communityCards = handinProgress ? this.table.communityCards() : null;
        
        this.tableState.areBettingRoundsCompleted = handinProgress ? this.table.areBettingRoundsCompleted() : null;
    }

    private addPlayer(publicKey: PublicKey, seatIndex: SeatIndex, buyIn: number)
    {
        console.log("Adding player with key " + publicKey + " to seat " + seatIndex + " with " + buyIn + " chips.");
        this.table.sitDown(seatIndex, buyIn);
        this.playerKeys.set(seatIndex, publicKey);
        this.playerSeats.set(publicKey, seatIndex);
        this.playerStates[seatIndex] = {
            holeCards: new Array<Card>(),
            chips: -1
        }
    }

    private getEmptySeats(): number[] {
        let emptySeats = new Array<number>();
        this.table.seats().forEach((seat, index) => {
            if (seat == null)
                emptySeats.push(index);
        });
        return emptySeats;
    }

    private getFilledSeats(): number[] {
        let filledSeats = new Array<number>();
        this.table.seats().forEach((seat, index) => {
            if (seat != null)
                filledSeats.push(index);
        });
        return filledSeats;
    }

    private getHandRanking(cards: Card[]): HandRanking {
        // TODO: calculate the hand ranking based on hole + community
        return HandRanking.HIGH_CARD;
    }
}
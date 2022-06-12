import math
import time
import heapq
import networkx as nx

from scipy.optimize import fsolve
import warnings

from network_import import *
from utils import PathUtils

warnings.filterwarnings('ignore', 'The iteration is not making good progress')

# For linkType
AV_LINK = 0
MIX_LINK = 1

class FlowTransportNetwork:

    def __init__(self):
        self.linkSet = {}
        self.mixLinkSet = {}
        self.nodeSet = {}

        self.tripSet = {}
        self.zoneSet = {}
        self.originZones = {}

        #自动驾驶流量比例
        self.avRate = 0.5
        self.hav = 1.0
        self.hcv = 1.8
        # self.networkx_graph = None

    # def to_networkx(self):
    #     if self.networkx_graph is None:
    #         self.networkx_graph = nx.DiGraph([(int(begin),int(end)) for (begin,end) in self.linkSet.keys()])
    #     return self.networkx_graph

    def reset_flow(self):
        for link in self.linkSet.values():
            link.reset_flow()
        for mixLink in self.mixLinkSet.values():
            mixLink.reset_flow()

    def reset(self):
        for link in self.linkSet.values():
            link.reset()
        for mixLink in self.mixLinkSet.values():
            mixLink.reset()


class Zone:
    def __init__(self, zoneId: str):
        self.zoneId = zoneId

        self.lat = 0
        self.lon = 0
        self.destList = []  # list of zone ids (strs)


class Node:
    """
    This class has attributes associated with any node
    """

    def __init__(self, nodeId: str):
        self.Id = nodeId
 
        self.lat = 0
        self.lon = 0

        self.outLinks = []  # list of node ids (strs)
        self.inLinks = []  # list of node ids (strs)

        # For CV Dijkstra
        self.CVLabel = np.inf
        self.CVPred = None
        # For AV Dijkstra
        self.AVLabel = np.inf
        self.AVPred = None
        # Indicate which type of link AV chosen
        self.linkType = 0


class Link:
    """
    This class has attributes associated with any link
    """

    def __init__(self,
                 init_node: str,
                 term_node: str,
                 capacity: float,
                 length: float,
                 fft: float,
                 b: float,
                 power: float,
                 speed_limit: float,
                #  toll: float,
                #  linkType,
                 lane_num = 10
                 ):
        self.init_node = init_node
        self.term_node = term_node
        self.max_capacity = float(capacity)  # veh per hour
        self.length = float(length)  # Length
        self.fft = float(fft)  # Free flow travel time (min)
        self.beta = float(power)
        self.alpha = float(b)
        # self.speedLimit = float(speed_limit)
        # self.toll = float(toll)
        # self.linkType = linkType # 1 indicates mix-flow link, 2 indicates av link
        self.lane_num = lane_num

        # self.curr_capacity_percentage = 1
        self.capacity = self.max_capacity
        self.flow = 0.0
        self.cost = self.fft

    # Method not used for assignment
    # def modify_capacity(self, delta_percentage: float):
    #     assert -1 <= delta_percentage <= 1
    #     self.curr_capacity_percentage += delta_percentage
    #     self.curr_capacity_percentage = max(0, min(1, self.curr_capacity_percentage))
    #     self.capacity = self.max_capacity * self.curr_capacity_percentage

    def reset(self):
        # self.curr_capacity_percentage = 1
        self.capacity = self.max_capacity
        self.reset_flow()

    def reset_flow(self):
        self.flow = 0.0
        self.cost = self.fft


class MixLink:
    """
    This class has attributes associated with any link with mix flow
    """

    def __init__(self,
                 init_node: str,
                 term_node: str,
                 capacity: float,
                 length: float,
                 fft: float,
                 b: float,
                 power: float,
                 speed_limit: float,
                #  toll: float,
                #  linkType,
                 lane_num = 10
                 ):
        self.init_node = init_node
        self.term_node = term_node
        self.max_capacity = float(capacity)  # veh per hour
        self.length = float(length)  # Length
        self.fft = float(fft)  # Free flow travel time (min)
        self.beta = float(power)
        self.alpha = float(b)
        # self.speedLimit = float(speed_limit)
        # self.toll = float(toll)
        # self.linkType = linkType # 1 indicates mix-flow link, 2 indicates av link
        self.lane_num = lane_num

        # self.curr_capacity_percentage = 1
        self.capacity = self.max_capacity
        self.cv_flow = 0.0
        self.av_flow = 0.0
        self.av_cost = self.fft
        self.cv_cost = self.fft

    # Method not used for assignment
    # def modify_capacity(self, delta_percentage: float):
    #     assert -1 <= delta_percentage <= 1
    #     self.curr_capacity_percentage += delta_percentage
    #     self.curr_capacity_percentage = max(0, min(1, self.curr_capacity_percentage))
    #     self.capacity = self.max_capacity * self.curr_capacity_percentage

    def reset(self):
        # self.curr_capacity_percentage = 1
        self.capacity = self.max_capacity
        self.reset_flow()

    def reset_flow(self):
        self.cv_flow = 0.0
        self.av_flow = 0.0
        self.cost = self.fft

class Demand:
    def __init__(self,
                 init_node: str,
                 term_node: str,
                 demand: float
                 ):
        self.fromZone = init_node
        self.toNode = term_node
        self.demand = float(demand)

# Dijkstra算法求解origin到路网中其他节点的最短(用时)路径, origin到s的最短用时存储在s.label中
def DijkstraHeap(origin, network: FlowTransportNetwork):
    """
    Calcualtes shortest path from an origin to all other destinations.
    The labels and preds are stored in node instances.
    """
    # 将路网中除origin节点外其他节点到origin的最短距离(时间)置为inf,将origin到origin的距离置为0
    for n in network.nodeSet:
        network.nodeSet[n].CVLabel = np.inf
        network.nodeSet[n].CVPred = None

        network.nodeSet[n].AVLabel = np.inf
        network.nodeSet[n].AVPred = None

    network.nodeSet[origin].CVLabel = 0.0
    network.nodeSet[origin].CVPred = None

    network.nodeSet[origin].AVLabel = 0.0
    network.nodeSet[origin].AVPred = None
    # SE is a heap
    # heapq按照元组的第一个元素排序成为小顶堆
    # 以origin节点作为初始当前节点
    SE = [(0, origin)]
    # SE中保存当前迭代轮次中待被选取的最短距离及相应节点
    while SE:
        # 每次取当前到origin最短距离最短点作为当前节点
        currentNode = heapq.heappop(SE)[1]
        # currentLabel 表示源节点到当前节点的最短距离
        currentLabel = network.nodeSet[currentNode].CVLabel
        # 对当前节点直接连接到的每个节点,更新其到origin的最短距离
        for toNode in network.nodeSet[currentNode].outLinks:
            link = (currentNode, toNode)
            newNode = toNode
            newPred = currentNode
            # 若将currentNode作为newNode的前驱节点情况下newNode到origin的距离更短,则更新newNode
            # 到origin的最短距离并更新newNode的前驱节点为currentNode
            existingLabel = network.nodeSet[newNode].CVLabel
            newLabel = currentLabel + network.mixLinkSet[link].cv_cost
            if newLabel < existingLabel:
                heapq.heappush(SE, (newLabel, newNode))
                network.nodeSet[newNode].CVLabel = newLabel
                network.nodeSet[newNode].CVPred = newPred

    # heapq按照元组的第一个元素排序成为小顶堆
    # 以origin节点作为初始当前节点
    SE = [(0, origin)]
    # SE中保存当前迭代轮次中待被选取的最短距离及相应节点
    while SE:
        # 每次取当前到origin最短距离最短点作为当前节点
        currentNode = heapq.heappop(SE)[1]
        # currentLabel 表示源节点到当前节点的最短距离
        currentLabel = network.nodeSet[currentNode].AVLabel
        # 对当前节点直接连接到的每个节点,更新其到origin的最短距离
        for toNode in network.nodeSet[currentNode].outLinks:
            link = (currentNode, toNode)
            newNode = toNode
            newPred = currentNode
            # 若将currentNode作为newNode的前驱节点情况下newNode到origin的距离更短,则更新newNode
            # 到origin的最短距离并更新newNode的前驱节点为currentNode
            existingLabel = network.nodeSet[newNode].AVLabel
            if network.mixLinkSet[link].av_cost < network.linkSet[link].cost:
                network.nodeSet[newNode].linkType = MIX_LINK
                newLabel = currentLabel + network.mixLinkSet[link].av_cost
            else:
                network.nodeSet[newNode].linkType = AV_LINK
                newLabel = currentLabel + network.linkSet[link].cost
            if newLabel < existingLabel:
                heapq.heappush(SE, (newLabel, newNode))
                network.nodeSet[newNode].AVLabel = newLabel
                network.nodeSet[newNode].AVPred = newPred

# 计算某一link的t
def BPRcostFunction(optimal: bool,
                    fft: float,
                    alpha: float,
                    flow: float,
                    capacity: float,
                    beta: float,
                    length: float,
                    # maxSpeed: float
                    ) -> float:
    if capacity < 1e-3:
        return np.finfo(np.float32).max
    if optimal:
        return fft * (1 + (alpha * math.pow((flow * 1.0 / capacity), beta)) * (beta + 1))
    return fft * (1 + alpha * math.pow((flow * 1.0 / capacity), beta))



def updateTravelTime(network: FlowTransportNetwork, optimal: bool = False, costFunction=BPRcostFunction):
    """
    This method updates the travel time on the links with the current flow
    """
    for l in network.linkSet:
        ra = 1.0
        network.linkSet[l].capacity = (3600.0 / (network.hav * ra)) * network.linkSet[l].lane_num
        network.linkSet[l].cost = costFunction(optimal,
                                               network.linkSet[l].fft,
                                               network.linkSet[l].alpha,
                                               network.linkSet[l].flow,
                                               network.linkSet[l].capacity,
                                               network.linkSet[l].beta,
                                               network.linkSet[l].length,
                                            #    network.linkSet[l].speedLimit
                                               )
    
    for l in network.mixLinkSet:
        # 仅当车道上车流量达到最低限度时更新车道的capacity和相应的cost time
        if network.mixLinkSet[l].av_flow + network.mixLinkSet[l].cv_flow < 0.0001:
            continue
        ra = (network.mixLinkSet[l].av_flow / (network.mixLinkSet[l].av_flow + network.mixLinkSet[l].cv_flow))
        network.mixLinkSet[l].capacity = (3600.0 / ((network.hav * ra) + (network.hcv * (1 - ra)))) * network.mixLinkSet[l].lane_num
        network.mixLinkSet[l].av_cost = costFunction(optimal,
                                               network.mixLinkSet[l].fft,
                                               network.mixLinkSet[l].alpha,
                                               network.mixLinkSet[l].av_flow,
                                               network.mixLinkSet[l].capacity,
                                               network.mixLinkSet[l].beta,
                                               network.mixLinkSet[l].length,
                                            #    network.linkSet[l].speedLimit
                                               )
        network.mixLinkSet[l].cv_cost = costFunction(optimal,
                                               network.mixLinkSet[l].fft,
                                               network.mixLinkSet[l].alpha,
                                               network.mixLinkSet[l].cv_flow,
                                               network.mixLinkSet[l].capacity,
                                               network.mixLinkSet[l].beta,
                                               network.mixLinkSet[l].length,
                                            #    network.linkSet[l].speedLimit
                                               )





def tracePreds(dest, network: FlowTransportNetwork):
    """
    返回两个值,cvSpLinks和avSpLinks
    分别表示cv和av在网络中的最短路径,avSpLinks列表中的第二项表示路径类型
    """
    avDest = cvDest = dest
    cvPrevNode = network.nodeSet[cvDest].CVPred
    cvSpLinks = []
    while cvPrevNode is not None:
        cvSpLinks.append((cvPrevNode, cvDest))
        cvDest = cvPrevNode
        cvPrevNode = network.nodeSet[cvDest].CVPred
    
    avPrevNode = network.nodeSet[avDest].AVPred
    avSpLinks = []
    while avPrevNode is not None:
        avSpLinks.append([(avPrevNode, avDest), network.nodeSet[avDest].linkType])
        avDest = avPrevNode
        avPrevNode = network.nodeSet[avDest].AVPred
    
    return cvSpLinks, avSpLinks

    # prevNode = network.nodeSet[dest].CVPred
    # spLinks = []
    # while prevNode is not None:
    #     spLinks.append((prevNode, dest))
    #     dest = prevNode
    #     prevNode = network.nodeSet[dest].CVPred
    # return spLinks

# SPTT --shortest path travel time
# TSTT --total system travel time
def loadAON(network: FlowTransportNetwork, computeXbar: bool = True):
    """
    This method produces auxiliary flows for all or nothing loading.
    """
    # av_link_x_bar为进行全1分配后av专用车道上的av流量字典
    av_link_x_bar = {l: 0.0 for l in network.linkSet}
    # mix_link_x_bar为进行全1分配后mix车道上,两种流量的字典,第一个值表示cv流量,第二个值表示av流量
    mix_link_x_bar = {l: [0.0, 0.0] for l in network.mixLinkSet}
    # x_av_bar = {l: 0.0 for l in network.mixLinkSet}
    CV_SPTT = 0.0
    AV_SPTT = 0.0
    for r in network.originZones:
        # 寻找r到网络各节点的最短用时
        # 对任一节点s: s.CVLabel--r到s只走mixLink最短用时即CV车辆最短用时  s.CVPred--s最短用时路径的直接前驱节点
        #           s.label1--r到s可走link或mixLink最短用时即AV车辆最短用时  s.AVPred--s最短用时路径的直接前驱节点
        DijkstraHeap(r, network=network)
        # 此时network.nodeSet[s].label保存r到s的最短用时
        for s in network.zoneSet[r].destList:
            dem = network.tripSet[r, s].demand
            av_dem = dem * network.avRate
            cv_dem = dem * (1 - network.avRate)
            if dem <= 0:
                continue

            CV_SPTT = CV_SPTT + network.nodeSet[s].CVLabel * cv_dem
            AV_SPTT = AV_SPTT + network.nodeSet[s].AVLabel * av_dem
            # 进行全1分配
            if computeXbar and r != s:
                cvSpLinks, avSpLinks = tracePreds(s, network)
                for spLink in cvSpLinks:
                    mix_link_x_bar[spLink][0] = mix_link_x_bar[spLink][0] + cv_dem
                for spLink in avSpLinks:
                    if spLink[1] == MIX_LINK: # 当前节点的AV最短路径前驱路径为mixLink
                        mix_link_x_bar[spLink[0]][1] = mix_link_x_bar[spLink[0]][1] + av_dem
                    elif spLink[1] == AV_LINK: # 当前节点AV的最短路径前驱路径为av专用link
                        av_link_x_bar[spLink[0]] = av_link_x_bar[spLink[0]] + av_dem
                    else:
                        print("loadAON err: link type\n")
                # for spLink in tracePreds(s, network):
                #     x_bar[spLink] = x_bar[spLink] + dem

    return CV_SPTT, AV_SPTT, mix_link_x_bar, av_link_x_bar

# 将demand读入到network的tripSet
def readDemand(demand_df: pd.DataFrame, network: FlowTransportNetwork):
    for index, row in demand_df.iterrows():

        init_node = str(int(row["init_node"]))
        term_node = str(int(row["term_node"]))
        demand = row["demand"]
        # print(row)
        network.tripSet[init_node, term_node] = Demand(init_node, term_node, demand)
        if init_node not in network.zoneSet:
            network.zoneSet[init_node] = Zone(init_node)
        if term_node not in network.zoneSet:
            network.zoneSet[term_node] = Zone(term_node)
        if term_node not in network.zoneSet[init_node].destList:
            network.zoneSet[init_node].destList.append(term_node)

    print(len(network.tripSet), "OD pairs")
    print(len(network.zoneSet), "OD zones")


def readNetwork(network_df: pd.DataFrame, network: FlowTransportNetwork):
    for index, row in network_df.iterrows():

        init_node = str(int(row["init_node"]))
        term_node = str(int(row["term_node"]))
        capacity = row["capacity"]
        length = row["length"]
        free_flow_time = row["free_flow_time"]
        b = row["b"]
        power = row["power"]
        speed = row["speed"]
        # toll = row["toll"]
        # link_type = row["link_type"]

        network.linkSet[init_node, term_node] = Link(init_node=init_node,
                                                     term_node=term_node,
                                                     capacity=capacity,
                                                     length=length,
                                                     fft=free_flow_time,
                                                     b=1.2, # alpha
                                                     power=5, # belta
                                                     speed_limit=speed,
                                                    #  toll=toll,
                                                    #  linkType=link_type
                                                     )
        network.mixLinkSet[init_node, term_node] = MixLink(init_node=init_node,
                                                     term_node=term_node,
                                                     capacity=capacity,
                                                     length=length,
                                                     fft=free_flow_time,
                                                     b=1.2, # alpha
                                                     power=5, # belta
                                                     speed_limit=speed,
                                                    #  toll=toll,
                                                    #  linkType=link_type
                                                     )

        if init_node not in network.nodeSet:
            network.nodeSet[init_node] = Node(init_node)
        if term_node not in network.nodeSet:
            network.nodeSet[term_node] = Node(term_node)
        if term_node not in network.nodeSet[init_node].outLinks:
            network.nodeSet[init_node].outLinks.append(term_node)
        if init_node not in network.nodeSet[term_node].inLinks:
            network.nodeSet[term_node].inLinks.append(init_node)

    print(len(network.nodeSet), "nodes")
    print(len(network.linkSet), "links")


def get_TSTT(network: FlowTransportNetwork, costFunction=BPRcostFunction, use_max_capacity: bool = True):
    TSTT = round(sum([network.linkSet[a].flow * costFunction(optimal=False,
                                                             fft=network.linkSet[
                                                                 a].fft,
                                                             alpha=network.linkSet[
                                                                 a].alpha,
                                                             flow=network.linkSet[
                                                                 a].flow,
                                                             capacity=network.linkSet[
                                                                 a].max_capacity if use_max_capacity else network.linkSet[
                                                                 a].capacity,
                                                             beta=network.linkSet[
                                                                 a].beta,
                                                             length=network.linkSet[
                                                                 a].length,
                                                            #  maxSpeed=network.linkSet[
                                                            #      a].speedLimit
                                                             ) for a in
                      network.linkSet]), 9)
    return TSTT


def assignment_loop(network: FlowTransportNetwork,
                    # algorithm: str = "FW",
                    systemOptimal: bool = False,
                    costFunction=BPRcostFunction,
                    accuracy: float = 0.001,
                    maxIter: int = 1000,
                    maxTime: int = 60,
                    verbose: bool = True):
    """
    For explaination of the algorithm see Chapter 7 of:
    https://sboyles.github.io/blubook.html
    PDF:
    https://sboyles.github.io/teaching/ce392c/book.pdf
    """
    network.reset_flow()

    iteration_number = 1
    av_gap = np.inf
    cv_gap = np.inf
    TSTT = np.inf
    assignmentStartTime = time.time()

    # Check if desired accuracy is reached
    while av_gap > accuracy or cv_gap > accuracy:
        # x_bar为新分配的link flow
        # Get x_bar throug all-or-nothing assignment
        _, _, mix_x_bar, av_x_bar = loadAON(network=network)

        # if algorithm == "MSA" or iteration_number == 1:
            # alpha = (1 / iteration_number)
        alpha = (1 / iteration_number)
        # elif algorithm == "FW":
        #     # If using Frank-Wolfe determine the step size alpha by solving a nonlinear equation
        #     alpha = findAlpha(x_bar,
        #                       network=network,
        #                       optimal=systemOptimal,
        #                       costFunction=costFunction)
        # else:
        #     print("Terminating the program.....")
        #     print("The solution algorithm ", algorithm, " does not exist!")
        #     raise TypeError('Algorithm must be MSA or FW')

        # Apply flow improvement
        for l in network.linkSet:
            network.linkSet[l].flow = alpha * av_x_bar[l] + (1 - alpha) * network.linkSet[l].flow
        for l in network.mixLinkSet:
            network.mixLinkSet[l].av_flow = alpha * mix_x_bar[l][1] + (1 - alpha) * network.mixLinkSet[l].av_flow
            network.mixLinkSet[l].cv_flow = alpha * mix_x_bar[l][0] + (1 - alpha) * network.mixLinkSet[l].cv_flow 

        # Compute the new travel time
        updateTravelTime(network=network,
                         optimal=systemOptimal,
                         costFunction=costFunction)

        # Compute the relative gap
        CV_SPTT, AV_SPTT, _, _ = loadAON(network=network, computeXbar=False)
        CV_SPTT = round(CV_SPTT, 9)
        AV_SPTT = round(AV_SPTT, 9)
        
        CV_TSTT = round(sum([network.mixLinkSet[a].cv_flow * network.mixLinkSet[a].cv_cost for a in 
                            network.mixLinkSet], 9))
        AV_TSTT = round((sum(network.linkSet[a].flow * network.linkSet[a].cost for a in network.linkSet) 
                        + sum(network.mixLinkSet[b].av_flow * network.mixLinkSet[b].av_cost for b in network.mixLinkSet)), 9)
        # TSTT = round(sum([network.linkSet[a].flow * network.linkSet[a].cost for a in
        #                   network.linkSet]), 9)

        # print(TSTT, SPTT, "TSTT, SPTT, Max capacity", max([l.capacity for l in network.linkSet.values()]))
        # gap = (TSTT / SPTT) - 1
        av_gap = (AV_TSTT / AV_SPTT) - 1
        cv_gap = (CV_TSTT / CV_SPTT) - 1
        if av_gap < 0 or cv_gap < 0:
            print("Error, gap is less than 0, this should not happen")
            # print("TSTT", "SPTT", TSTT, SPTT)

            # Uncomment for debug

            # print("Capacities:", [l.capacity for l in network.linkSet.values()])
            # print("Flows:", [l.flow for l in network.linkSet.values()])

        # Compute the real total travel time (which in the case of system optimal rounting is different from the TSTT above)
        # TSTT = get_TSTT(network=network, costFunction=costFunction)

        iteration_number += 1
        if iteration_number > maxIter:
            if verbose:
                print(
                    "The assignment did not converge to the desired gap and the max number of iterations has been reached")
                print("Assignment took", round(time.time() - assignmentStartTime, 5), "seconds")
                print("Current cv gap:", round(cv_gap, 5))
                print("Current av gap:", round(av_gap, 5))
            return CV_TSTT, AV_TSTT
        if time.time() - assignmentStartTime > maxTime:
            if verbose:
                print("The assignment did not converge to the desired gap and the max time limit has been reached")
                print("Assignment did ", iteration_number, "iterations")
                print("Current cv gap:", round(cv_gap, 5))
                print("Current av gap:", round(av_gap, 5))
            return CV_TSTT, AV_TSTT

    if verbose:
        print("Assignment converged in ", iteration_number, "iterations")
        print("Assignment took", round(time.time() - assignmentStartTime, 5), "seconds")
        print("Current cv gap:", round(cv_gap, 5))
        print("Current av gap:", round(av_gap, 5))

    return CV_TSTT, AV_TSTT


def writeResults(network: FlowTransportNetwork, output_file: str, costFunction=BPRcostFunction,
                 systemOptimal: bool = False, verbose: bool = True):
    outFile = open(output_file, "w")
    TSTT = get_TSTT(network=network, costFunction=costFunction)
    if verbose:
        print("\nTotal system travel time:", f'{TSTT} secs')
    tmpOut = "Total Travel Time:\t" + str(TSTT)
    outFile.write(tmpOut + "\n")
    tmpOut = "Cost function used:\t" + BPRcostFunction.__name__
    outFile.write(tmpOut + "\n")
    tmpOut = ["User equilibrium (UE) or system optimal (SO):\t"] + ["SO" if systemOptimal else "UE"]
    outFile.write("".join(tmpOut) + "\n\n")
    tmpOut = "init_node\tterm_node\tflow\ttravelTime"
    outFile.write(tmpOut + "\n")
    for i in network.linkSet:
        tmpOut = str(network.linkSet[i].init_node) + "\t" + str(
            network.linkSet[i].term_node) + "\t" + str(
            network.linkSet[i].flow) + "\t" + str(costFunction(False,
                                                               network.linkSet[i].fft,
                                                               network.linkSet[i].alpha,
                                                               network.linkSet[i].flow,
                                                               network.linkSet[i].max_capacity,
                                                               network.linkSet[i].beta,
                                                               network.linkSet[i].length,
                                                            #    network.linkSet[i].speedLimit
                                                               ))
        outFile.write(tmpOut + "\n")
    outFile.close()


def load_network(net_file: str,
                 demand_file: str = None,
                 force_net_reprocess: bool = False,
                 verbose: bool = True
                 ) -> FlowTransportNetwork:
    readStart = time.time()

    if demand_file is None:
        demand_file = '_'.join(net_file.split("_")[:-1] + ["trips.tntp"])

    net_name = net_file.split("/")[-1].split("_")[0]

    if verbose:
        print(f"Loading network {net_name}...")

    net_df, demand_df = import_network(
        net_file,
        demand_file,
        force_reprocess=force_net_reprocess
    )

    # cv_network = FlowTransportNetwork()
    # av_network = FlowTransportNetwork()
    network = FlowTransportNetwork()

    readDemand(demand_df, network=network)
    readNetwork(net_df, network=network)

    network.originZones = set([k[0] for k in network.tripSet])

    if verbose:
        print("Network", net_name, "loaded")
        print("Reading the network data took", round(time.time() - readStart, 2), "secs\n")

    return network


def computeAssingment(net_file: str,
                      demand_file: str = None,
                    #   algorithm: str = "FW",  # FW or MSA
                      costFunction=BPRcostFunction,
                      systemOptimal: bool = False,
                      accuracy: float = 0.0001,
                      maxIter: int = 1000,
                      maxTime: int = 60,
                      results_file: str = None,
                      force_net_reprocess: bool = False,
                      verbose: bool = True
                      ) -> float:
    """
    This is the main function to compute the user equilibrium UE (default) or system optimal (SO) traffic assignment
    All the networks present on https://github.com/bstabler/TransportationNetworks following the tntp format can be loaded


    :param net_file: Name of the network (net) file following the tntp format (see https://github.com/bstabler/TransportationNetworks)
    :param demand_file: Name of the demand (trips) file following the tntp format (see https://github.com/bstabler/TransportationNetworks), leave None to use dafault demand file
    :param algorithm:
           - "FW": Frank-Wolfe algorithm (see https://en.wikipedia.org/wiki/Frank%E2%80%93Wolfe_algorithm)
           - "MSA": Method of successive averages
           For more information on how the algorithms work see https://sboyles.github.io/teaching/ce392c/book.pdf
    :param costFunction: Which cost function to use to compute travel time on edges, currently available functions are:
           - BPRcostFunction (see https://rdrr.io/rforge/travelr/man/bpr.function.html)
           - greenshieldsCostFunction (see Greenshields, B. D., et al. "A study of traffic capacity." Highway research board proceedings. Vol. 1935. National Research Council (USA), Highway Research Board, 1935.)
           - constantCostFunction
    :param systemOptimal: Wheather to compute the system optimal flows instead of the user equilibrium
    :param accuracy: Desired assignment precision gap
    :param maxIter: Maximum nuber of algorithm iterations
    :param maxTime: Maximum seconds allowed for the assignment
    :param results_file: Name of the desired file to write the results,
           by default the result file is saved with the same name as the input network with the suffix "_flow.tntp" in the same folder
    :param force_net_reprocess: True if the network files should be reprocessed from the tntp sources
    :param verbose: print useful info in standard output
    :return: Totoal system travel time
    """

    network = load_network(net_file=net_file, demand_file=demand_file, verbose=verbose, force_net_reprocess=force_net_reprocess)

    if verbose:
        print("Computing assignment...")
    # TSTT = assignment_loop(network=network, algorithm=algorithm, systemOptimal=systemOptimal, costFunction=costFunction,
    #                        accuracy=accuracy, maxIter=maxIter, maxTime=maxTime, verbose=verbose)
    CV_TSTT, AV_TSTT = assignment_loop(network=network, systemOptimal=systemOptimal, costFunction=costFunction,
                            accuracy=accuracy, maxIter=maxIter, maxTime=maxTime, verbose=verbose)
    if results_file is None:
        results_file = '_'.join(net_file.split("_")[:-1] + ["flow.tntp"])

    # writeResults(network=network,
    #              output_file=results_file,
    #              costFunction=costFunction,
    #              systemOptimal=systemOptimal,
    #              verbose=verbose)

    return CV_TSTT, AV_TSTT


if __name__ == '__main__':

    # This is an example usage for calculating System Optimal and User Equilibrium with Frank-Wolfe

    net_file = str(PathUtils.chicago_net_file)
    # net_file = str(PathUtils.braess_net_file)
    # total_system_travel_time_optimal = computeAssingment(net_file=net_file,
    #                                                      algorithm="FW",
    #                                                      costFunction=BPRcostFunction,
    #                                                      systemOptimal=True,
    #                                                      verbose=True,
    #                                                      accuracy=0.00001,
    #                                                      maxIter=1000,
    #                                                      maxTime=6000000)

    total_cv_travel_time_equilibrium, total_av_travel_time_equilibrium = computeAssingment(net_file=net_file,
                                                            #  algorithm="MSA",
                                                             costFunction=BPRcostFunction,
                                                             systemOptimal=False,
                                                             verbose=True,
                                                             accuracy=0.01,
                                                             maxIter=1000,
                                                             maxTime=60000)
    print("total_cv_travel_time_equilibrium: ", total_cv_travel_time_equilibrium)
    print("total_av_travel_time_equilibrium: ", total_av_travel_time_equilibrium)
    # print("UE - SO = ", total_system_travel_time_equilibrium - total_system_travel_time_optimal)

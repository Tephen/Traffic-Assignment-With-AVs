import math
from mimetypes import init
from random import random
from tabnanny import verbose
import time
import heapq
from unittest.mock import DEFAULT
import networkx as nx

from scipy.optimize import fsolve
import warnings

from network_import import *
from utils import PathUtils

import csv
import jenkspy
warnings.filterwarnings('ignore', 'The iteration is not making good progress')

# For linkType
AV_LINK = 0
MIX_LINK = 1

# 每部署多少条AV车道进行一次UE
UE_ITERNAL = 40

# 默认道路条数的种类数
NB_CLASS = 6

# 不同部署阶段对应的avRate和avLengthLimit
deployStage =\
{
    0 : [0.05, 0],
    1 : [0.05, 0.1],
    2 : [0.15, 0.2],
    3 : [0.25, 0.3],
    4 : [0.35, 0.4],
    5 : [0.45, 0.5],
    6 : [0.55, 0.6],
    7 : [0.65, 0.7],
    8 : [0.75, 0.8],
    9 : [0.85, 0.9],
}

class FlowTransportNetwork:

    def __init__(self):
        self.avLinkSet = {}
        self.mixLinkSet = {}
        self.nodeSet = {}

        self.tripSet = {}
        self.zoneSet = {}
        self.originZones = {}

        # 自动驾驶流量比例
        self.avRate = 0.0
        # 自动驾驶车道长度限制
        self.avLengthLimit = 0.0
        self.hav = 1.0
        self.hcv = 1.8
        # self.hcv = 1.0
        self.avLinkTotalLength = 0.0
        self.linkTotalLength = 0.0
        # self.networkx_graph = None


    def reset_flow(self):
        for link in self.avLinkSet.values():
            link.reset_flow()
        for mixLink in self.mixLinkSet.values():
            mixLink.reset_flow()

    def reset(self):
        for link in self.avLinkSet.values():
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
                 lane_num :int
                 ):
        self.init_node = init_node
        self.term_node = term_node
        self.max_capacity = float(capacity)  # veh per hour
        self.length = float(length)  # Length
        self.fft = float(fft)  # Free flow travel time 
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


    def reset(self):
        # self.curr_capacity_percentage = 1
        self.capacity = self.max_capacity
        self.reset_flow()

    def reset_flow(self):
        self.flow = 0.0
        # self.cost = self.fft
        # 0车道时cost设为无穷大
        # self.cost = np.finfo(np.float32).max
        self.cost = 1e+30


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
                 lane_num :int
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
        self.cost = self.fft
        # self.cv_cost = self.fft


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


def DeployOneLane(network: FlowTransportNetwork, link):
    """
    在给定的mixlink中转化一条车道为AV车道
    """
    if(network.mixLinkSet[link].lane_num < 2):
        # print(f"less than 2 lane2 on {link}")
        return
    else:
        network.mixLinkSet[link].lane_num -= 1
        network.avLinkSet[link].lane_num += 1
        network.avLinkTotalLength += network.avLinkSet[link].length
        return

def computeIttc(network: FlowTransportNetwork, link):
    """
    计算瞬时总行程时间差
    """
    original_total_time = network.mixLinkSet[link].cost * (network.mixLinkSet[link].av_flow+network.mixLinkSet[link].cv_flow) + \
                          network.avLinkSet[link].cost * network.avLinkSet[link].flow
    # original_total_time = network.mixLinkSet[link].cost + network.avLinkSet[link].cost
    # 若mixlink上所有av车辆转移到avlink上后mixlink的tt
    ra = 0.0
    capacity = (3600.0 / ((network.hav * ra) + (network.hcv * (1 - ra)))) * (network.mixLinkSet[link].lane_num-1)
    ta1 = BPRcostFunction(False,
                            network.mixLinkSet[link].fft,
                            network.mixLinkSet[link].alpha,
                            network.mixLinkSet[link].cv_flow,
                            capacity,
                            network.mixLinkSet[link].beta,
                            network.mixLinkSet[link].length,
                            )
    # 若mixlink上所有av车辆转移到avlink上后avlink的tt
    ra = 1.0
    capacity = (3600.0 / (network.hav * ra)) * (network.avLinkSet[link].lane_num+1)
    tan1 = BPRcostFunction(False,
                            network.avLinkSet[link].fft,
                            network.avLinkSet[link].alpha,
                            (network.avLinkSet[link].flow+network.mixLinkSet[link].av_flow),
                            capacity,
                            network.avLinkSet[link].beta,
                            network.avLinkSet[link].length,
                            )
    # 所有av车辆均移动到avlink
    if ta1 >= tan1:
        new_total_time = ta1 * network.mixLinkSet[link].cv_flow +\
                        tan1 * (network.avLinkSet[link].flow + network.mixLinkSet[link].av_flow)
    # 部分av车辆移动到avlink
    else:
        # print(f"network.mixLinkSet[link].lane_num:{network.mixLinkSet[link].lane_num}")
        # print(f"network.avLinkSet[link].lane_num:{network.avLinkSet[link].lane_num}")
        # print(f"network.mixLinkSet[link].av_flow:{network.mixLinkSet[link].av_flow}")
        # print(f"network.mixLinkSet[link].cv_flow:{network.mixLinkSet[link].cv_flow}")
        # print(f"network.avLinkSet[link].flow:{network.avLinkSet[link].flow}")
        b = (((network.mixLinkSet[link].lane_num-1) * network.hav * (network.mixLinkSet[link].av_flow+network.avLinkSet[link].flow)) \
            - ((network.avLinkSet[link].lane_num+1) * network.hcv * network.mixLinkSet[link].cv_flow))\
                / (network.hav * 4)
        # print(f"b={b}")
        ra = b / (network.mixLinkSet[link].cv_flow + b)
        capacity = (3600.0 / ((network.hav * ra) + (network.hcv * (1 - ra)))) * (network.mixLinkSet[link].lane_num-1)
        ta2 = BPRcostFunction(False,
                            network.mixLinkSet[link].fft,
                            network.mixLinkSet[link].alpha,
                            (network.mixLinkSet[link].cv_flow + b),
                            capacity,
                            network.mixLinkSet[link].beta,
                            network.mixLinkSet[link].length,
                            )
        ra = 1.0
        capacity = (3600.0 / (network.hav * ra)) * (network.avLinkSet[link].lane_num+1)
        tan2 = BPRcostFunction(False,
                            network.avLinkSet[link].fft,
                            network.avLinkSet[link].alpha,
                            (network.avLinkSet[link].flow + network.mixLinkSet[link].av_flow - b),
                            capacity,
                            network.avLinkSet[link].beta,
                            network.avLinkSet[link].length,
                            )
        # print(f"ta2{ta2}, tan2{tan2}")
        # new_total_time = ta2 + tan2
        new_total_time = ta2 * (network.mixLinkSet[link].cv_flow + b) +\
                        tan2 * (network.avLinkSet[link].flow + network.mixLinkSet[link].av_flow - b)
        


    return new_total_time - original_total_time

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
            newLabel = currentLabel + network.mixLinkSet[link].cost
            if newLabel < existingLabel:
                heapq.heappush(SE, (newLabel, newNode))
                network.nodeSet[newNode].CVLabel = newLabel
                network.nodeSet[newNode].CVPred = newPred

    # heapq按照元组的第一个元素排序成为小顶堆
    # 以origin节点作为初始当前节点
    SEA = [(0, origin)]
    # SE中保存当前迭代轮次中待被选取的最短距离及相应节点
    while SEA:
        # 每次取当前到origin最短距离最短点作为当前节点
        currentNode = heapq.heappop(SEA)[1]
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
            if network.mixLinkSet[link].cost < network.avLinkSet[link].cost:
                newLabel = currentLabel + network.mixLinkSet[link].cost
                if newLabel < existingLabel:
                    network.nodeSet[newNode].linkType = MIX_LINK
                    heapq.heappush(SEA, (newLabel, newNode))
                    network.nodeSet[newNode].AVLabel = newLabel
                    network.nodeSet[newNode].AVPred = newPred
            else:
                newLabel = currentLabel + network.avLinkSet[link].cost
                if newLabel < existingLabel:
                    network.nodeSet[newNode].linkType = AV_LINK
                    heapq.heappush(SEA, (newLabel, newNode))
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
        # return np.finfo(np.float32).max
        return 1e+30
    if optimal:
        return fft * (1 + (alpha * math.pow((flow * 1.0 / capacity), beta)) * (beta + 1))
    return fft * (1 + alpha * math.pow((flow * 1.0 / capacity), beta))



def updateTravelTime(network: FlowTransportNetwork, optimal: bool = False, costFunction=BPRcostFunction):
    """
    This method updates the travel time on the links with the current flow
    """
    for l in network.avLinkSet:
        ra = 1.0
        network.avLinkSet[l].capacity = (3600.0 / (network.hav * ra)) * network.avLinkSet[l].lane_num
        network.avLinkSet[l].cost = costFunction(optimal,
                                               network.avLinkSet[l].fft,
                                               network.avLinkSet[l].alpha,
                                               network.avLinkSet[l].flow,
                                               network.avLinkSet[l].capacity,
                                               network.avLinkSet[l].beta,
                                               network.avLinkSet[l].length,
                                               )

    
    for l in network.mixLinkSet:
        # 仅当车道上车流量达到最低限度时更新车道的capacity和相应的cost time
        if network.mixLinkSet[l].av_flow + network.mixLinkSet[l].cv_flow == 0.0:
            continue
        ra = (network.mixLinkSet[l].av_flow / (network.mixLinkSet[l].av_flow + network.mixLinkSet[l].cv_flow))
        network.mixLinkSet[l].capacity = (3600.0 / ((network.hav * ra) + (network.hcv * (1 - ra)))) * network.mixLinkSet[l].lane_num
        network.mixLinkSet[l].cost = costFunction(optimal,
                                               network.mixLinkSet[l].fft,
                                               network.mixLinkSet[l].alpha,
                                               (network.mixLinkSet[l].av_flow + network.mixLinkSet[l].cv_flow),
                                               network.mixLinkSet[l].capacity,
                                               network.mixLinkSet[l].beta,
                                               network.mixLinkSet[l].length,
                                               )






def tracePreds(dest, network: FlowTransportNetwork):
    """
    返回两个值,cvSpLinks和avSpLinks
    分别表示cv和av在网络中的最短路径,avSpLinks列表中的第二项表示路径类型
    路径类型0代表AV专用车道,1代表混合车道
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
    av_link_x_bar = {l: 0.0 for l in network.avLinkSet}
    # mix_link_x_bar为进行全1分配后mix车道上,两种流量的字典,第一个值表示cv流量,第二个值表示av流量
    mix_link_x_bar = {l: [0.0, 0.0] for l in network.mixLinkSet}
    # x_av_bar = {l: 0.0 for l in network.mixLinkSet}
    # CV_SPTT = 0.0
    # AV_SPTT = 0.0
    SPTT = 0.0
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

            # CV_SPTT = CV_SPTT + network.nodeSet[s].CVLabel * cv_dem
            # AV_SPTT = AV_SPTT + network.nodeSet[s].AVLabel * av_dem
            SPTT = SPTT + network.nodeSet[s].CVLabel * cv_dem
            SPTT = SPTT + network.nodeSet[s].AVLabel * av_dem
            # 进行全1分配
            if computeXbar and r != s:
                cvSpLinks, avSpLinks = tracePreds(s, network)
                # print(f'OD对{r}-->{s}之间cv与av的最短路径')
                # print("0--AV专用车道  1--混合车道")
                # print("cvSpLinks")
                # print(cvSpLinks)
                # print("avSpLinks")
                # print(avSpLinks)
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

    return SPTT, mix_link_x_bar, av_link_x_bar

# 将demand读入到network的tripSet
def readDemand(demand_df: pd.DataFrame, network: FlowTransportNetwork):
    for index, row in demand_df.iterrows():
        # print(row)
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
    # 获取自然间断点
    breaks = jenkspy.jenks_breaks(network_df["capacity"], nb_class=NB_CLASS)
    # print(breaks)
    for index, row in network_df.iterrows():
        init_node = str(int(row["init_node"]))
        term_node = str(int(row["term_node"]))
        capacity = row["capacity"]
        length = row["length"]
        free_flow_time = row["free_flow_time"]
        # 处理数据中fft为0的路段
        if free_flow_time == 0.0:
            free_flow_time = 0.1
        b = row["b"]
        power = row["power"]
        speed = row["speed"]
        # lane_num = DEFAULT_LANENUM;
        lane_num = 0
        # print(breaks)
        for i in range(NB_CLASS):
            if breaks[i] <= capacity <= breaks[i+1]:
                lane_num = i + 2
                break
        # print(f"lane_num on {init_node}-{term_node} is {lane_num}")
        network.linkTotalLength += length


        network.avLinkSet[init_node, term_node] = Link(init_node=init_node,
                                                    term_node=term_node,
                                                    capacity=capacity,
                                                    length=length,
                                                    fft=free_flow_time,
                                                    b=1.2, # alpha
                                                    power=5, # belta
                                                    speed_limit=speed,
                                                    lane_num=0
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
                                                    lane_num=lane_num
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
    print(len(network.avLinkSet), "links")


def get_TSTT(network: FlowTransportNetwork, costFunction=BPRcostFunction, use_max_capacity: bool = True):
    TSTT = round(sum([network.avLinkSet[a].flow * costFunction(optimal=False,
                                                             fft=network.avLinkSet[
                                                                 a].fft,
                                                             alpha=network.avLinkSet[
                                                                 a].alpha,
                                                             flow=network.avLinkSet[
                                                                 a].flow,
                                                             capacity=network.avLinkSet[
                                                                 a].max_capacity if use_max_capacity else network.avLinkSet[
                                                                 a].capacity,
                                                             beta=network.avLinkSet[
                                                                 a].beta,
                                                             length=network.avLinkSet[
                                                                 a].length,
                                                            #  maxSpeed=network.avLinkSet[
                                                            #      a].speedLimit
                                                             ) for a in
                      network.avLinkSet]), 3)
    return TSTT


def assignment_loop(network: FlowTransportNetwork,
                    # algorithm: str = "FW",
                    systemOptimal: bool = False,
                    costFunction=BPRcostFunction,
                    accuracy: float = 0.001,
                    maxIter: int = 100,
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
    # av_gap = np.inf
    # cv_gap = np.inf
    gap = np.inf
    TSTT = np.inf
    assignmentStartTime = time.time()

    # Check if desired accuracy is reached
    while gap > accuracy:
        # x_bar为新分配的link flow
        # Get x_bar throug all-or-nothing assignment
        # print(f"{iteration_number}th mix travel time")
        # print([network.mixLinkSet[a].cost for a in network.mixLinkSet])
        # print(f"{iteration_number}th av travel time")
        # print([network.avLinkSet[a].cost for a in network.avLinkSet])
        _, mix_x_bar, av_x_bar = loadAON(network=network)
        # print("mix_x_bar")
        # print(mix_x_bar)
        # print("########################")
        # print("av_x_bar")
        # print(av_x_bar)
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
        # print("New flow on av link")
        for l in network.avLinkSet:
            network.avLinkSet[l].flow = alpha * av_x_bar[l] + (1 - alpha) * network.avLinkSet[l].flow
            network.avLinkSet[l].flow = round(network.avLinkSet[l].flow, 2)
            # print(f"{network.avLinkSet[l].flow} on {l}")
        # print("New flow on mix link")
        for l in network.mixLinkSet:
            network.mixLinkSet[l].av_flow = alpha * mix_x_bar[l][1] + (1 - alpha) * network.mixLinkSet[l].av_flow
            network.mixLinkSet[l].cv_flow = alpha * mix_x_bar[l][0] + (1 - alpha) * network.mixLinkSet[l].cv_flow
            network.mixLinkSet[l].av_flow = round(network.mixLinkSet[l].av_flow, 2)
            network.mixLinkSet[l].cv_flow = round(network.mixLinkSet[l].cv_flow, 2) 
            # print(f"{network.mixLinkSet[l].av_flow}av and {network.mixLinkSet[l].cv_flow}cv on {l}")

        # Compute the new travel time
        updateTravelTime(network=network,
                         optimal=systemOptimal,
                         costFunction=costFunction)

        # Compute the relative gap
        SPTT, _, _ = loadAON(network=network, computeXbar=False)
        SPTT = round(SPTT, 3)

        
        CV_TSTT = round(sum([network.mixLinkSet[a].cv_flow * network.mixLinkSet[a].cost for a in 
                            network.mixLinkSet]), 3)
        AV_TSTT = round((sum([network.avLinkSet[a].flow * network.avLinkSet[a].cost for a in network.avLinkSet])  
                        + sum([network.mixLinkSet[b].av_flow * network.mixLinkSet[b].cost for b in network.mixLinkSet])), 3)

        TSTT = CV_TSTT + AV_TSTT

        # print(TSTT, SPTT, "TSTT, SPTT, Max capacity", max([l.capacity for l in network.avLinkSet.values()]))
        # gap = (TSTT / SPTT) - 1
        # av_gap = (AV_TSTT / AV_SPTT) - 1
        # cv_gap = (CV_TSTT / CV_SPTT) - 1
        gap = (TSTT / SPTT) - 1
        if gap < 0:
            print("Error, gap is less than 0, this should not happen")
            # print("TSTT", "SPTT", TSTT, SPTT)


        iteration_number += 1
        if iteration_number > maxIter:
            # if verbose:
            #     print(
            #         "The assignment did not converge to the desired gap and the max number of iterations has been reached")
            #     print("Assignment took", round(time.time() - assignmentStartTime, 5), "seconds")
            #     print("Current gap:", round(gap, 5))
            #     print(f"current TSTT:{TSTT}")
                # print("Current av gap:", round(av_gap, 5))
            return TSTT
        if time.time() - assignmentStartTime > maxTime:
            if verbose:
                print("The assignment did not converge to the desired gap and the max time limit has been reached")
                print("Assignment did ", iteration_number, "iterations")
                print("Current gap:", round(gap, 5))
                print(f"current TSTT:{TSTT}")
                # print("Current av gap:", round(av_gap, 5))
            return TSTT

    if verbose:
        print("Assignment converged in ", iteration_number, "iterations")
        print("Assignment took", round(time.time() - assignmentStartTime, 5), "seconds")
        print("Current gap:", round(gap, 5))
        print(f"current TSTT:{TSTT}")
        # print("Current av gap:", round(av_gap, 5))

    return TSTT


def writeResults(deployIter, network: FlowTransportNetwork, output_file: str, TSTT: float, costFunction=BPRcostFunction,
                 systemOptimal: bool = False, verbose: bool = True):
    '''
    保存结果到文件中
    '''
    # with open(output_file, "a") as outFile:
    with open(output_file, "a", encoding="utf-8-sig") as csvFile:
        outFile = csv.writer(csvFile)
        # TSTT = get_TSTT(network=network, costFunction=costFunction)
        if verbose:
            # print("\nTotal system travel time:", f'{TSTT} secs')
            print("Total system travel time:", f'TSTT: {TSTT}')

        tmpOut = ["\n" + str(deployIter) + "阶段部署"]
        outFile.writerow(tmpOut)
        tmpOut = ["当前阶段AV市场率: " + str(deployStage[deployIter][0]) + "\t当前阶段AV车道长度百分比限制: " + str(deployStage[deployIter][1])]
        outFile.writerow(tmpOut)
        tmpOut = ["Total system travel time:" + str(TSTT)]
        outFile.writerow(tmpOut)
        tmpOut = ["AV-Dedicated Link Flow:"]
        outFile.writerow(tmpOut)

        tmpOut = ["出发点"]
        for i in network.avLinkSet:
            tmpOut.append(str(network.avLinkSet[i].init_node))
        outFile.writerow(tmpOut)
        tmpOut = ["到达点"]
        for i in network.avLinkSet:
            tmpOut.append(str(network.avLinkSet[i].term_node))
            # tmpOut += "\t"
        outFile.writerow(tmpOut)
        tmpOut = ["车流量"]
        for i in network.avLinkSet:
            tmpOut.append(str(network.avLinkSet[i].flow))
            # tmpOut += "\t"
        outFile.writerow(tmpOut)
        tmpOut = ["车道数"]
        for i in network.avLinkSet:
            tmpOut.append(str(network.avLinkSet[i].lane_num))
            # tmpOut += "\t"
        outFile.writerow(tmpOut)
        tmpOut = ["通行时间"]
        for i in network.avLinkSet:
            tmpOut.append(str(network.avLinkSet[i].cost))
            # tmpOut += "\t"
        outFile.writerow(tmpOut)

        tmpOut = ["Mix-Flow Link Flow:"]
        outFile.writerow(tmpOut)
        tmpOut = ["出发点"]
        for i in network.mixLinkSet:
            tmpOut.append(str(network.mixLinkSet[i].init_node))
            # tmpOut += "\t"
        outFile.writerow(tmpOut)
        tmpOut = ["到达点"]
        for i in network.mixLinkSet:
            tmpOut.append(str(network.mixLinkSet[i].term_node))
            # tmpOut += "\t"
        outFile.writerow(tmpOut)
        tmpOut = ["AV车流量"]
        for i in network.mixLinkSet:
            tmpOut.append(str(network.mixLinkSet[i].av_flow))
            # tmpOut += "\t"
        outFile.writerow(tmpOut)
        tmpOut = ["CV车流量"]
        for i in network.mixLinkSet:
            tmpOut.append(str(network.mixLinkSet[i].cv_flow))
            # tmpOut += "\t"
        outFile.writerow(tmpOut)
        tmpOut = ["车道数"]
        for i in network.avLinkSet:
            tmpOut.append(str(network.mixLinkSet[i].lane_num))
            # tmpOut += "\t"
        outFile.writerow(tmpOut)
        tmpOut = ["通行时间"]
        for i in network.avLinkSet:
            tmpOut.append(str(network.mixLinkSet[i].cost))
            # tmpOut += "\t"
        outFile.writerow(tmpOut)



def load_network(net_file: str,
                 demand_file: str = None,
                 force_net_reprocess: bool = False,
                 verbose: bool = True
                 ) -> FlowTransportNetwork:
    readStart = time.time()

    if demand_file is None:
        demand_file = '_'.join(net_file.split("_")[:-1] + ["trips.tntp"])

    import sys
    if sys.platform.startswith('win'):
        net_name = net_file.split("\\")[-1].split("_")[0]
    else:
        net_name = net_file.split("/")[-1].split("_")[0]

    if verbose:
        print(f"Loading network {net_name}...")

    net_df, demand_df = import_network(
        net_file,
        demand_file,
        force_reprocess=force_net_reprocess
    )
    # print("net_df")
    # print(net_df)
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


def computeAssingment(network: FlowTransportNetwork,
                    #   demand_file: str = None,
                    #   algorithm: str = "FW",  # FW or MSA
                      costFunction=BPRcostFunction,
                      systemOptimal: bool = False,
                      accuracy: float = 0.0001,
                      maxIter: int = 5,
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

    # network = load_network(net_file=net_file, demand_file=demand_file, verbose=verbose, force_net_reprocess=force_net_reprocess)

    # if verbose:
    #     print("Computing assignment...")
    # TSTT = assignment_loop(network=network, algorithm=algorithm, systemOptimal=systemOptimal, costFunction=costFunction,
    #                        accuracy=accuracy, maxIter=maxIter, maxTime=maxTime, verbose=verbose)
    TSTT = assignment_loop(network=network, systemOptimal=systemOptimal, costFunction=costFunction,
                            accuracy=accuracy, maxIter=maxIter, maxTime=maxTime, verbose=verbose)
    # if results_file is None:
    #     results_file = '_'.join(net_file.split("_")[:-1] + ["flow.tntp"])

    # writeResults(network=network,
    #              output_file=results_file,
    #              costFunction=costFunction,
    #              systemOptimal=systemOptimal,
    #              verbose=verbose,
    #              TSTT=TSTT)

    return TSTT


def deploy_loop(network: FlowTransportNetwork,
                    # algorithm: str = "FW",
                    systemOptimal: bool = False,
                    costFunction=BPRcostFunction,
                    accuracy: float = 0.001,
                    maxIter: int = 25,
                    maxTime: int = 6000,
                    verbose: bool = True,
                    results_file = None,
                    deployIter: int = 0):
    """
    部署AV车道
    """
    network.avRate = deployStage[deployIter][0]
    network.avLengthLimit = deployStage[deployIter][1]
    timeToUE = 0
    deployNum = 0
    while True:
    # 1. 求解UE问题

        if timeToUE == 0:
            TSTT = computeAssingment(network=network,
                            costFunction=costFunction,
                            systemOptimal=systemOptimal,
                            verbose=verbose,
                            accuracy=accuracy,
                            maxIter=maxIter,
                            maxTime=maxTime)
        candidateDict = {}
    # 2. 构建可选部署AV车道集合
        # if verbose:
        #     print("构建可部署车道集合...")
        for mix_l in network.mixLinkSet:
            # 检查剩余车道数和AV车道总长度限制
            if (network.mixLinkSet[mix_l].lane_num > 1) and \
                ((network.mixLinkSet[mix_l].length + network.avLinkTotalLength) / network.linkTotalLength <= network.avLengthLimit):
                # 只保留瞬时tt变化<0的备选车道位置
                if computeIttc(network=network, link = mix_l) <= 0:
                    candidateDict[mix_l] = computeIttc(network=network, link = mix_l)
    # 3. 当无可部署AV车道时,结束算法
        if len(candidateDict) == 0:
            if verbose:
                print(f"所有车道总长为{network.linkTotalLength}")
                print(f"AV车道限长为{network.linkTotalLength*network.avLengthLimit},当前AV车道总长已达{network.avLinkTotalLength}")
                print("没有可部署车道")
                break
    # 4. 对可部署的混合link按ittc从小到大排序
        candidateList = sorted(candidateDict.items(), key = lambda kv:(kv[1], kv[0]))
    # 5. 选取ittc最小的mixlink部署一条AV车道
        timeToUE += 1
        timeToUE %= UE_ITERNAL
        deployNum += 1  
        DeployOneLane(network=network, link = candidateList[0][0])

    # 结束本阶段部署并保存数据 
    TSTT = computeAssingment(network=network,
                            costFunction=costFunction,
                            systemOptimal=systemOptimal,
                            verbose=verbose,
                            accuracy=accuracy,
                            maxIter=maxIter,
                            maxTime=maxTime)   
    if verbose:
        print(f"{deployIter}阶段共部署{deployNum}条车道")
        print(f"{deployIter}阶段部署结束, 写入结果...")
    writeResults(deployIter=deployIter,       
                        network=network,
                        output_file=results_file,
                        costFunction=costFunction,
                        systemOptimal=systemOptimal,
                        verbose=verbose,
                        TSTT=TSTT)
  

import time
if __name__ == '__main__':

    # This is an example usage for calculating System Optimal and User Equilibrium with Frank-Wolfe

    net_file = str(PathUtils.chicago_net_file)
    # net_file = str(PathUtils.anaheim_net_file)
    # net_file = str(PathUtils.braess_net_file)
    # net_file = str(PathUtils.test_net_file)
    # net_file = str(PathUtils.winnipeg_net_file)
    results_file = '_'.join(net_file.split("_")[:-1] + ["flow.csv"])
    results_file = results_file.replace("tntp_networks", "assignment_results")
    network = load_network(net_file=net_file)

    g_start_time = time.time()
    for i in range(10):
        start_time = time.time()
        print("#######################")
        print(f"第{i}阶段部署")
        deploy_loop(network=network, results_file=results_file, deployIter=i)
        end_time = time.time()
        time_sec = end_time - start_time
        m, s = divmod(time_sec, 60)
        h, m = divmod(m, 60)
        print(f"第{i}阶段结束, 本阶段用时: {h}hour {m}min {s}sec")
        print("#######################\n")
    g_end_time = time.time()
    g_time_sec = g_end_time - g_start_time
    m, s = divmod(time_sec, 60)
    h, m = divmod(m, 60)
    print(f"总用时: {h}hour {m}min {s}sec")
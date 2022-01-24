import heapq





def binary_tree_to_adj_list(tree):
    graph = {}



def djikstra(graph, source_node):
    dist, prev = {v: float('inf') for v in graph}, {}
    dist[source_node] = 0

    Q = [(0, source_node)]
    while len(Q) > 0:
        current_dist, current_node = heapq.heappop(Q)
        for neighbor_node, edge_weight in graph[current_node]:
            new_dist = dist[current_node] + edge_weight
            if new_dist < dist[neighbor_node]:
                dist[neighbor_node], prev[neighbor_node] = new_dist, current_node
                heapq.heappush(Q, (new_dist, neighbor_node))

    return dist, prev



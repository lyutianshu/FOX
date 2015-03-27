/*SCD is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  SCD is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program.  If not, see <http://www.gnu.org/licenses/>.
  */

#include <algorithm>
#include <assert.h>
#include <cmath>
#include <common/time.h>
#include <communities/communities.h>
#include <fstream>
#include <graph/graph.h>
#include <iostream>
#include <map>
#include <omp.h>
#include <sstream>
#include <string.h>
#include <sys/time.h>
#include <time.h>
#include <vector>
#include <queue>
#include <wcc/wcc.h>

namespace scd {

#define SCD_INVALID_COMMUNITY 0xffffffff
	std::vector< std::vector<uint32_t> > d;
    uint32_t num_threads = 1;
    /** @brief Types of movements.*/
    enum MovementType {
        E_REMOVE,
        E_REMOVE_AND_INSERT,
        E_NO_MOVEMENT,
		E_COPY    //复制节点
    };

    /** @brief This struct represents a movement.*/
    struct Movement {
        MovementType m_MovementType;
        uint32_t m_NodeId;
        uint32_t m_Community;
        uint32_t m_src;
    };

    /** @brief Compares two node clustering.
     *  @param e1 Void pointer to the first node clustering.    
     *  @param e2 Void pointer to the second node clustering.   
     *  @return -1 if e1 goes before e2. 1 if e1 goes after e2. 0 if e1 and e2 are equal.*/
    static int Compare_NodeClusterings(const void* e1, const void* e2) {
        NodeClustering* nC1 = (NodeClustering*) e1;
        NodeClustering* nC2 = (NodeClustering*) e2;
        if (nC1->m_CC > nC2->m_CC) return -1;
        if (nC1->m_CC < nC2->m_CC) return 1;
        if (nC1->m_Degree > nC2->m_Degree) return -1;
        if (nC1->m_Degree < nC2->m_Degree) return 1;
        return 0;
    }

    /** @brief Compares two unsigned integers.
     *  @param e1 Void pointer to the first unsigned integer.   
     *  @param e2 Void pointer to the second unsigned integer.  
     *  @return -1 if e1 goes before e2. 1 if e1 goes after e2. 0 if e1 and e2 are equal.*/
    static int Compare_Ids(const void* e1, const void* e2) {
        uint32_t id1 = *(uint32_t*) e1;
        uint32_t id2 = *(uint32_t*) e2;
        if (id1 < id2) return -1;
        if (id2 < id1) return 1;
        return 0;
    }

    /** @brief this function is used to compress the laberl space of a partition in order to be comprissed between
     *           0 and the actual number of communities - 1.
     *  @param[in] graph The graph where the partition belongs.
     *  @param[in] communities The array of current labels.
     *  @param[out] destCommunities The array where the new labeling will be stored.*/
    static uint32_t CompressCommunityLabels(const CGraph* graph, std::vector<uint32_t> &communities, std::vector<uint32_t> &destCommunities) {
        std::map<uint32_t, uint32_t> * map = new std::map<uint32_t, uint32_t>();
        uint32_t label = 0;
        for (uint32_t i = 0; i < communities.size(); i++) {
            if (!map->count(communities[i])) {
                map->insert(std::pair<uint32_t, uint32_t>(communities[i], label));
                label++;
            }
        }

		destCommunities.erase(destCommunities.begin(),destCommunities.end());
        for (uint32_t i = 0; i < communities.size(); i++) {
            destCommunities.push_back((*(map->find(communities[i]))).second);
        }
        delete map;
        return label;
    }

    /** @brief Initializes a partition structure from a labels to communities array.
     *  @param[in] graph The graph where the partition belongs.
     *  @param[out] partition The partition structure where the partition will be stored.
     *  @param[in] communities The array of nodes to community labels from which the partition is initialized.*/
    static uint32_t InitializeFromLabelsArray(const CGraph* graph, CommunityPartition* partition, 
                                              std::vector <uint32_t> &communities, std::map<uint32_t,uint32_t> &NodeIndices,
											  std::multimap<uint32_t,uint32_t> &RNodeIndices) {

        partition->m_CommunityIndices = NULL;
        partition->m_Communities = NULL;
        partition->m_InternalEdges = NULL;
        partition->m_ExternalEdges = NULL;
        partition->m_NodeWCC = NULL;
        partition->m_NumCommunities = 0;
        partition->m_WCC = 0;

		if(!NodeIndices.empty())
			partition->m_NumNodes = graph->GetNumNodes()+NodeIndices.size();
        else
			partition->m_NumNodes = graph->GetNumNodes();
	
        uint32_t maxNumCommunities = 0;
        for (uint32_t i = 0; i < partition->m_NumNodes; i++) {
            if (communities[i] > maxNumCommunities) {
                maxNumCommunities = communities[i];
            }
        }
        maxNumCommunities++;
		/**< @brief The number of communities.*/
        partition->m_NumCommunities = CompressCommunityLabels(graph, communities, partition->m_NodeLabels);

        //Allocating space to store the communities/**< @brief The array of indices for each label into the community array.*/
        partition->m_CommunityIndices = new uint32_t[partition->m_NumCommunities];
        if (!partition->m_CommunityIndices) {
            printf("Error allocating labels indices.\n");
            return 1;
        }
		/**< @brief The communities.*/
        partition->m_Communities = new uint32_t[partition->m_NumCommunities + partition->m_NumNodes];
        if (!partition->m_Communities) {
            printf("Error allocating inverted index.\n");
            return 1;
        }
	
        partition->m_NodeWCC = new double64_t[partition->m_NumNodes];
        if (!partition->m_NodeWCC) {
            printf("Error allocating node labels %u.\n", partition->m_NumNodes);
            return 1;
        }

        //Creating the counters the creation of the inverted index 
        uint32_t* counters = new uint32_t[partition->m_NumCommunities];
		double64_t* CommunityCopySize = new double64_t[partition->m_NumCommunities];
        if (!counters) {
            printf("Error allocating counters: %u\n", partition->m_NumCommunities);
            return 1;
        }

#pragma omp parallel for schedule(SCD_SCHEDULING, SCD_THREAD_BLOCK_SIZE)
        for (uint32_t i = 0; i < partition->m_NumCommunities; i++) {
            counters[i] = 0;
			CommunityCopySize[i] = 0;
        }	
        //Computing community sizes;
        for (uint32_t i = 0; i < partition->m_NumNodes; i++) {
            counters[partition->m_NodeLabels[i]]++;
			uint32_t tmp=i;
			if(i >= graph->GetNumNodes()){
				 tmp=(*NodeIndices.find(i)).second;
			}
			uint32_t c = RNodeIndices.count(tmp);
			if( c == 0 )
				CommunityCopySize[partition->m_NodeLabels[i]]++;
			else
				CommunityCopySize[partition->m_NodeLabels[i]] += 1.0f/(double64_t)c;
        }	
        
        uint32_t currentIndex = 0;
        for (uint32_t i = 0; i < partition->m_NumCommunities; i++) {
            if (counters[i] > 0) {
                partition->m_CommunityIndices[i] = currentIndex;
                partition->m_Communities[currentIndex] = counters[i];
                currentIndex += counters[i] + 1;
            } else {
                partition->m_CommunityIndices[i] = SCD_INVALID_COMMUNITY;
            }
            counters[i] = 0;
        }
        //Initializing the inverted index.
        for (uint32_t i = 0; i < partition->m_NumNodes; i++) {
            uint32_t lIndex = partition->m_CommunityIndices[partition->m_NodeLabels[i]];
            assert(lIndex != SCD_INVALID_COMMUNITY);
            assert(counters[partition->m_NodeLabels[i]] < partition->m_Communities[lIndex]);
            if(i<graph->GetNumNodes())
                partition->m_Communities[lIndex + counters[partition->m_NodeLabels[i]] + 1] = i;
            else
			{
                partition->m_Communities[lIndex + counters[partition->m_NodeLabels[i]] + 1] = (*NodeIndices.find(i)).second;
			}

			counters[partition->m_NodeLabels[i]]++;
        }

        for (uint32_t i = 0; i < partition->m_NumCommunities; i++) {
            if (partition->m_CommunityIndices[i] != SCD_INVALID_COMMUNITY) {
                uint32_t lIndex = partition->m_CommunityIndices[i];
                qsort(&(partition->m_Communities[lIndex + 1]), partition->m_Communities[lIndex], sizeof (uint32_t), Compare_Ids);
            }
        }
        delete[] counters;
	
        partition->m_InternalEdges = new uint32_t[partition->m_NumCommunities];
        if (!partition->m_InternalEdges) {
            printf("Error while allocating internal edges.\n");
            return 1;
        }

        partition->m_ExternalEdges = new uint32_t[partition->m_NumCommunities];
        if (!partition->m_ExternalEdges) {
            printf("Error while allocating external edges.\n");
            return 1;
        }

#pragma omp parallel for schedule(SCD_SCHEDULING, SCD_THREAD_BLOCK_SIZE)
        for (uint32_t i = 0; i < partition->m_NumCommunities; i++) {
            partition->m_InternalEdges[i] = 0;
            partition->m_ExternalEdges[i] = 0;
        }
	
        for (uint32_t i = 0; i < partition->m_NumNodes; i++) {
            uint32_t degree;
            const uint32_t* adjacencies;
            if(i<graph->GetNumNodes()){
               adjacencies = graph->GetNeighbors(i);
               degree = graph->GetDegree(i);
           }
            else{
                adjacencies = graph->GetNeighbors((*NodeIndices.find(i)).second);
                degree = graph->GetDegree((*NodeIndices.find(i)).second);
            }
            for (uint32_t j = 0; j < degree; j++) {
                if (partition->m_NodeLabels[i] == partition->m_NodeLabels[adjacencies[j]]) {
                    partition->m_InternalEdges[partition->m_NodeLabels[i]]++;
                } else {
                    partition->m_ExternalEdges[partition->m_NodeLabels[i]]++;
                    partition->m_ExternalEdges[partition->m_NodeLabels[adjacencies[j]]]++;
                }
            }
        }
	
//        partition->m_WCC = ComputeWCC(graph, partition->m_NodeLabels, partition->m_NumCommunities, partition->m_CommunityIndices, partition->m_Communities, partition->m_NodeWCC, NodeIndices, RNodeIndices, CommunityCopySize);//wcc重写
			
        return 0;
    }

    /** @brief Computes the increment on WCC for inserting a node into a community.
      r				The size of the community.
      d_in			The number of edges between the inserted vertex and the community.
      d_out			The number of edges between the inserted vertex and the rest of the graph.
      c_out 		The number of edges leaving the community (note that this MUST include d_in).
      p_ext_node 	The probability that two edges of the vertex pointing to the rest of the graph close a triangle.
      p_in 			The probability that an edge inside of the community exists.
      p_ext 		The probability that two edges leaving the community close a triangle.
	  p_edge 		The probability that an edge between two vertex outside the community exists.*/
    static double64_t CheckForIncrement(int32_t r, int32_t d_in, int32_t d_out, uint32_t c_out, double64_t p_ext_node, double64_t p_in, double64_t p_ext, double64_t p_edge,uint32_t semiTriangle) {
        double64_t t;
        if (r > 0) {
            t = (c_out - d_in) / (double64_t) r;
        } else {
            t = 0.0;
        }
        double64_t A = 0.0;
        double64_t denom = 0.0;
		if(!semiTriangle){
			denom = (0.5*d_in * (d_in - 1) * p_in + 0.5*d_out * (d_out - 1) * p_ext_node);
			if (denom != 0.0 && ((r + d_out) > 0)) {
				A = (0.5*(d_in * (d_in - 1) * p_in) / denom) * (d_in + d_out) / (double64_t) (r + d_out);
			}
			double64_t BMinus = 0.0;
			denom = 0.5*(r - 1)*(r - 2) * p_in * p_in * p_in + (d_in - 1) * p_in + t * (r - 1) * p_in * p_ext + 0.5*t * (t - 1) * p_ext + (d_out) * p_ext;

			if (denom != 0.0 && ((r + t) > 0)) {
				BMinus = (((d_in - 1) * p_in) / denom) * ((r - 1) * p_in + 1 + t) / (r + t);
			}
			double64_t CMinus = 0.0;
			denom =0.5*(r - 1)*(r - 2) * p_in * p_in * p_in + t * (t - 1) * p_ext + t * (r - 1)*(p_in) * p_ext;
			if (denom != 0.0 && ((r + t) > 0) && ((r - 1 + t) > 0)) {
				CMinus = -((0.5*(r - 1)*(r - 2) * p_in * p_in * p_in) / denom) * ((r - 1) * p_in + t) / ((r + t)*(r - 1 + t));
			}
			return (A + d_in * BMinus + (r - d_in) * CMinus);
		}
		
		else{
			denom = d_in * r * p_in + d_out * p_edge;
			if (denom != 0.0 && ((r + d_out) > 0)) {
				A = (d_in * r * p_in / denom) * (d_in + d_out) / (double64_t) (r + d_out);
			}
			double64_t BMinus = 0.0;
			denom = 0.5 *(r - 1)*(r - 2) * p_in * p_in + (d_in - 1) + t * (r - 1) * p_in + t * p_edge + d_out;
			if (denom != 0.0 && ((r + t) > 0)) {
				BMinus = (((d_in - 1) * p_in) / denom) * ((r - 1) * p_in + 1 + t) / (r + t);
			}
			double64_t CMinus = 0.0;
			denom = 0.5 *(r - 1)*(r - 2) * p_in * p_in + t * (r - 1) * p_in + t * p_edge ;
			if (denom != 0.0 && ((r + t) > 0) && ((r - 1 + t) > 0)) {
				CMinus = -((0.5*(r - 1)*(r - 2) * p_in * p_in ) / denom) * ((r - 1) * p_in + t) / ((r + t)*(r - 1 + t));
			}
			return (A + d_in * BMinus + (r - d_in) * CMinus);
		}
		

    }

    /** @brief Checks the best movement of a vertex.
      @param[in] graph The graph.
      @param[in] node The node to check the movement.
      @param[in] partition The current partition into communities.
      @return The movement to perform.*/
    static Movement CheckForBestMovement(const CGraph* graph, uint32_t node, CommunityPartition* partition,
                                         std::map<uint32_t, uint32_t>&NodeIndices,
										 std::multimap<uint32_t, uint32_t>&RNodeIndices,
										 uint32_t semiTriangle,const std::vector<uint32_t>&tempNodeLabels,
										 uint32_t N) {

        Movement movement;
        movement.m_MovementType = E_NO_MOVEMENT;
        movement.m_NodeId       = node;

        std::map<uint32_t, uint32_t> neighborsCommunity;
//        neighborsCommunity.insert(std::pair<uint32_t, uint32_t>(partition->m_NodeLabels[node], 0));
		neighborsCommunity.insert(std::pair<uint32_t, uint32_t>(tempNodeLabels[node], 0));
        const uint32_t * adjacencies ;
        uint32_t degree ;

        if(node < graph->GetNumNodes()){
            adjacencies = graph->GetNeighbors(node);
            degree = graph->GetDegree(node);   
        }
        else{
            adjacencies = graph->GetNeighbors((*NodeIndices.find(node)).second);
            degree = graph->GetDegree((*NodeIndices.find(node)).second);   
        }

        for (uint32_t i = 0; i < degree; i++) {
            uint32_t neighbor = adjacencies[i];
            if (partition->m_Communities[partition->m_CommunityIndices[tempNodeLabels[neighbor]]] > 1) {
                std::map<uint32_t, uint32_t>::iterator it = neighborsCommunity.find(tempNodeLabels[neighbor]);
                if (it != neighborsCommunity.end()) {
                    (*it).second++;
                } else {
                    neighborsCommunity.insert(std::pair<uint32_t, uint32_t>(tempNodeLabels[neighbor], 1));
                }
            }
			typedef std::multimap<uint32_t,uint32_t>::iterator psrc;
			std::pair<psrc, psrc> pos = RNodeIndices.equal_range(neighbor);
			while(pos.first != pos.second){
				if(pos.first->second < N){
				if( partition->m_Communities[partition->m_CommunityIndices[tempNodeLabels[pos.first->second]]] > 1){			
					std::map<uint32_t, uint32_t>::iterator it = neighborsCommunity.find(tempNodeLabels[pos.first->second]);
					if (it != neighborsCommunity.end()) {
						(*it).second++;
					} else {
						neighborsCommunity.insert(std::pair<uint32_t, uint32_t>(tempNodeLabels[pos.first->second], 1));
					}
				}
				}
				++pos.first;
			}
        }

        bool removeCommunity = false;
        uint32_t bestRemoveInternalEdges = 0;
        uint32_t auxInternalEdges = (*neighborsCommunity.find(tempNodeLabels[node])).second;
        uint32_t community = tempNodeLabels[node];
        uint32_t communityIndex = partition->m_CommunityIndices[community];
        uint32_t communitySize = partition->m_Communities[communityIndex];
        double64_t p_in;
        if ((communitySize - 2) != 0 && (communitySize - 1) != 0) {
			p_in = (partition->m_InternalEdges[community] - auxInternalEdges * 2) / ((double64_t) (communitySize - 1) * (communitySize - 2));
		} else {
            p_in = 0.0f;
        }
        double64_t p_ext = graph->GetCC();
        double64_t p_ext_node = p_ext;
        double64_t bestRemoveImprovement;
        bestRemoveImprovement = -CheckForIncrement(communitySize - 1, auxInternalEdges,
                degree - auxInternalEdges,
                partition->m_ExternalEdges[community]/2 + auxInternalEdges - (degree - auxInternalEdges),
                p_ext_node, p_in, p_ext,graph->GetEdgesProbablity(),semiTriangle);
        bestRemoveInternalEdges = auxInternalEdges;
 
		if (bestRemoveImprovement >=0.0f){
            removeCommunity = true;
        }


        uint32_t   bestInsertCommunity;
        double64_t bestInsertImprovement      = -10000000000000.0;		
        uint32_t   bestInsertInternalEdges    = 0;
        bool       insertCommunity            = false;
		bool       copyCommunity              = false;

       for (std::map<uint32_t, uint32_t>::iterator it = neighborsCommunity.begin(); it != neighborsCommunity.end(); ++it) {
            uint32_t community = it->first;
            if (community != tempNodeLabels[node]) {
                uint32_t auxInternalEdges = it->second;
                uint32_t communityIndex   = partition->m_CommunityIndices[community];
                uint32_t communitySize    = partition->m_Communities[communityIndex];
                double64_t p_in;
                if ((communitySize - 1) > 0 && (communitySize > 0)) {
					p_in = (partition->m_InternalEdges[community]) / ((double64_t) (communitySize) * (communitySize - 1));
				} else {
                    p_in = 0.0;
                }

                double64_t p_ext          = graph->GetCC();
                double64_t p_ext_node     = p_ext;
                double64_t auxImprovement = CheckForIncrement(communitySize, auxInternalEdges, degree - auxInternalEdges,
                        partition->m_ExternalEdges[community]/2, p_ext_node, p_in, p_ext,graph->GetEdgesProbablity(),semiTriangle);
				if(removeCommunity){
					if (auxImprovement>0 && auxImprovement + bestRemoveImprovement > bestInsertImprovement) {
						insertCommunity = true;
						bestInsertImprovement = auxImprovement + bestRemoveImprovement;
						bestInsertCommunity = community;
						bestInsertInternalEdges = auxInternalEdges;
					}
				}
				else{
					if (auxImprovement>0 && auxImprovement - bestRemoveImprovement > bestInsertImprovement) {
						copyCommunity = true;
						bestInsertImprovement = auxImprovement - bestRemoveImprovement;
						bestInsertCommunity = community;
						bestInsertInternalEdges = auxInternalEdges;

					}
				}
            }
        }

		if(insertCommunity){
			uint32_t tmp=node;
			if(node >= graph->GetNumNodes()){
				node=(*NodeIndices.find(node)).second;
			}
			if( partition->m_NodeLabels[node] == bestInsertCommunity ){
				if(partition->m_Communities[partition->m_CommunityIndices[partition->m_NodeLabels[movement.m_NodeId]]] == 1)
					return movement;
				movement.m_MovementType =E_REMOVE;
				return movement;
			}
			typedef std::multimap<uint32_t,uint32_t>::iterator psrc;
			std::pair<psrc, psrc> pos = RNodeIndices.equal_range(node);
			uint32_t c = RNodeIndices.count(node);
			while(pos.first != pos.second){
				if( partition->m_NodeLabels[pos.first->second]== bestInsertCommunity ){
					if(partition->m_Communities[partition->m_CommunityIndices[partition->m_NodeLabels[movement.m_NodeId]]] == 1)
						return movement;
					movement.m_MovementType =E_REMOVE;
					return movement;
				}
				++pos.first;
			}
            movement.m_MovementType = E_REMOVE_AND_INSERT;
            movement.m_Community = bestInsertCommunity;
			partition->m_NodeLabels[tmp]=bestInsertCommunity;	
        }
		else if(copyCommunity){	
			if(node >= graph->GetNumNodes()){
				node=(*NodeIndices.find(node)).second;
			}
			if( partition->m_NodeLabels[node]== bestInsertCommunity ){
				return movement;
			}
			typedef std::multimap<uint32_t,uint32_t>::iterator psrc;
			std::pair<psrc, psrc> pos = RNodeIndices.equal_range(node);
			uint32_t c = RNodeIndices.count(node);
			while(pos.first != pos.second){
				if( partition->m_NodeLabels[pos.first->second]== bestInsertCommunity )
					return movement;
				++pos.first;
			}

			if( NodeIndices.size()==0 )
				movement.m_NodeId = graph->GetNumNodes();
			else{
				std::map<uint32_t,uint32_t>::iterator it;
				it = NodeIndices.end();
				it--;
				movement.m_NodeId = it->first + 1 ;
			}
            NodeIndices.insert(std::pair<uint32_t, uint32_t>(movement.m_NodeId, node));
			RNodeIndices.insert(std::pair<uint32_t,uint32_t>(node, movement.m_NodeId));
			partition->m_NodeLabels.push_back(bestInsertCommunity);
			if(partition->m_NodeLabels.size()!=movement.m_NodeId+1)
			printf("error!\n");
			if(movement.m_NodeId<=N)
			printf("Nerror!\n");
			movement.m_src = node;
            movement.m_MovementType = E_COPY;
            movement.m_Community = bestInsertCommunity;
        }
		
		else if(removeCommunity){
			if(partition->m_Communities[partition->m_CommunityIndices[partition->m_NodeLabels[movement.m_NodeId]]] == 1)
				return movement;
/*			std::map<uint32_t,uint32_t>::iterator it;
			it = NodeIndices.find(node);
			if(it!=NodeIndices.end()){
				typedef std::multimap<uint32_t,uint32_t>::iterator psrc;
				std::pair<psrc, psrc> pos = RNodeIndices.equal_range(it->second);
				while(pos.first != pos.second){
					if( pos.first->second == it->first ){
						RNodeIndices.erase(pos.first);
						break;
					}
				++pos.first;
				}
				NodeIndices.erase(it);
			}*/
			movement.m_MovementType =E_REMOVE;
			return movement;
		}

        return movement;
    }


    /** @brief Performs an improvement step, that is, checks for movements for all the nodes and
      and computes the new partitions.
      @param[in] graph The graph.
      @param[out] partition The current partition. It will be modified with the new partition.*/
    static uint32_t PerformImprovementStep(const CGraph* graph, CommunityPartition* partition,
										   std::map<uint32_t,uint32_t>& NodeIndices,
										   std::multimap <uint32_t, uint32_t> &RNodeIndices,
										   uint32_t semiTriangle) {
        std::vector<Movement>* movements = new std::vector<Movement>[num_threads];
        uint32_t N = graph->GetNumNodes()+NodeIndices.size();  //遍历所有节点，原图节点数+新增节点数

        std::vector <uint32_t> tempNodeLabels(partition->m_NodeLabels);
        uint32_t noMovements = 0;
//#pragma omp parallel for schedule(SCD_SCHEDULING,SCD_THREAD_BLOCK_SIZE) 
        for (uint32_t i = 0; i < N; i++) {
            int thread = omp_get_thread_num();
            if (i % 100000 == 0) {
                printf("Checked movements of %d nodes.", i);
				printf("\r");
            }
            Movement movement; 
            movement = CheckForBestMovement(graph, i, partition,NodeIndices,RNodeIndices,semiTriangle,tempNodeLabels,N);
            if (movement.m_MovementType != E_NO_MOVEMENT) {
                movements[thread].push_back(movement);
			}
			else
				noMovements++;
        }

        printf("All movements checked\n");

        uint32_t totalMovements = 0;
        uint32_t removeMovements = 0;
        uint32_t removeAndInsertMovements = 0;
        uint32_t insertMovements = 0;
        uint32_t copyMovements = 0;     

		uint32_t extraLabel;
#pragma omp parallel for schedule(static,1)   
        for (uint32_t thread = 0; thread < num_threads; thread++) {
            uint32_t numMovements = movements[thread].size();
            totalMovements += numMovements;
            uint32_t nextLabelThread = partition->m_NumCommunities + numMovements * thread;   

            for (uint32_t i = 0; i < numMovements; i++) {
                Movement movement = (movements[thread])[i];
                switch (movement.m_MovementType) {
                    case E_REMOVE:
                        tempNodeLabels[movement.m_NodeId] = nextLabelThread;
                        removeMovements++;
                        nextLabelThread++;
						extraLabel=nextLabelThread;
                        break;
                    case E_REMOVE_AND_INSERT:
                        if (partition->m_Communities[partition->m_CommunityIndices[tempNodeLabels[movement.m_NodeId]]] == 1) {
                            insertMovements++;
                        } else {
                            removeAndInsertMovements++;
                        }
						tempNodeLabels[movement.m_NodeId] = movement.m_Community;
                        break;
                    case E_COPY:						
                        tempNodeLabels.push_back(movement.m_Community);
						if(tempNodeLabels.size()!=movement.m_NodeId+1)
							printf("error in insert!");
                        copyMovements++;
                        break;
                }
            }
        }
        delete [] movements;
        printf(" Number of removes performed: %d\n", removeMovements);
        printf(" Number of remove and insert performed: %d\n", removeAndInsertMovements);
        printf(" Number of insert performed: %d\n", insertMovements);
        printf(" Number of copy performed: %d\n", copyMovements);
        printf(" Number of nothing performed: %d\n", noMovements);		
        FreeResources(partition);
		
        if (InitializeFromLabelsArray(graph, partition, tempNodeLabels,NodeIndices,RNodeIndices)) {
            printf("Error initializing from label array.\n");
            return 1;
        }
/*			std::vector <uint32_t> tmpNodeLabels(partition->m_NodeLabels);
            const uint32_t* adjacencies1;
            uint32_t        degree1;
			uint32_t countnum = 0;
			extraLabel = partition->m_NumCommunities+1;
            for (uint32_t h = 0; h < partition->m_NumCommunities; h++) {
                if (partition->m_CommunityIndices[h] != SCD_INVALID_COMMUNITY) {
                    uint32_t* community = &partition->m_Communities[partition->m_CommunityIndices[h] + 1];
                    uint32_t communitySize = partition->m_Communities[partition->m_CommunityIndices[h]];
                    uint32_t flag=0;  

                	uint32_t d[500][500];
					memset(d,0,sizeof(d));
					
					for (uint32_t i = 0; i < communitySize; i++){
						const uint32_t* adjacencies1 = graph->GetNeighbors(community[i]);
						uint32_t degree1 = graph->GetDegree(community[i]);
						for (uint32_t j = 0; j < communitySize; j++){
							if (i == j){
//								d[i].insert(j);
								d[i][j] = 1;
								continue;
							}						
							uint32_t*  currentNode1     = (uint32_t*) adjacencies1;
							uint32_t*  endAdjacencies1  = (uint32_t*) adjacencies1 + degree1;
							while (currentNode1 != endAdjacencies1){
                                if(*currentNode1==community[j]){
									d[i][j] = 1;
//									d[i].insert(j);
									flag++;
									break;
								}
                                currentNode1++;
                            }
						}
					}
					
					std::vector<uint32_t> mark(communitySize,0);
					std::queue<uint32_t> q;
					q.push(0);
					uint32_t conn_num = 0;
					mark[0] = 1;
					while (!q.empty()){
						uint32_t t = q.front();
						q.pop();
						conn_num++;
						for (uint32_t i = 0; i < communitySize; i++)
							if (d[t][i] == 1 && mark[i] == 0){
//							if(d[t].find(i)!=d[t].end() && mark[i]==0){
								q.push(i);
								mark[i] = 1;
							}
					}

					if (conn_num != communitySize){
						for(uint32_t n = 0; n < communitySize; n++){
							if(tmpNodeLabels[community[n]]==h)
								tmpNodeLabels[community[n]]=extraLabel++;
							else{
								typedef std::multimap<uint32_t,uint32_t>::iterator psrc;
								std::pair<psrc, psrc> pos = RNodeIndices.equal_range(community[n]);
								while(pos.first != pos.second){
									if(tmpNodeLabels[pos.first->second] == h){
										tmpNodeLabels[pos.first->second]=extraLabel++;
										break;
									}
									++pos.first;
								}
							}	
						}
						countnum++;
					}
				}
            }
			printf("delete disconnected community:%d\n",countnum);
            InitializeFromLabelsArray(graph, partition, tmpNodeLabels,NodeIndices,RNodeIndices);*/
		if((double64_t)noMovements/(double64_t)N > 0.99f ){
			//remove the isolated node from the community
			//delete unconnected community
/*		    std::vector <uint32_t> tmpNodeLabels(partition->m_NodeLabels);
            const uint32_t* adjacencies1;
            uint32_t        degree1;
            for (uint32_t i = 0; i < partition->m_NumCommunities; i++) {
                if (partition->m_CommunityIndices[i] != SCD_INVALID_COMMUNITY) {
                    uint32_t* community = &partition->m_Communities[partition->m_CommunityIndices[i] + 1];
                    uint32_t communitySize = partition->m_Communities[partition->m_CommunityIndices[i]];
                    uint32_t flag=0;  
                        for (uint32_t j = 0; j < communitySize; j++) {
                            adjacencies1 = graph->GetNeighbors(community[j]);
                            degree1 = graph->GetDegree(community[j]);   
                            uint32_t flag_j=flag;
                            for (uint32_t k = 0; k < communitySize; k++) {  
								if(j==k)
									continue;
                                uint32_t*  currentNode1     = (uint32_t*) adjacencies1;
                                uint32_t*  endAdjacencies1  = (uint32_t*) adjacencies1 + degree1;
            
                                while (currentNode1 != endAdjacencies1){
                                    if(*currentNode1==community[k])
                                        flag++;
                                    currentNode1++;
                                }                     
                            }
							flag_j=flag-flag_j;
                            if(flag_j==0){
								if(tmpNodeLabels[community[j]]==i)
									tmpNodeLabels[community[j]]=extraLabel++;
								else{
								typedef std::multimap<uint32_t,uint32_t>::iterator psrc;
								std::pair<psrc, psrc> pos = RNodeIndices.equal_range(community[j]);
								while(pos.first != pos.second){
									if(tmpNodeLabels[pos.first->second] == i){
										tmpNodeLabels[pos.first->second]=extraLabel++;
										break;
									}
									++pos.first;
								}
								if(pos.first == pos.second)
									printf("error happen when delete single node!!!\n");
								}	
							}		
                        }
                    if(flag/2<communitySize){
						for(uint32_t n = 0; n < communitySize; n++){
							if(tmpNodeLabels[community[n]]==i)
								tmpNodeLabels[community[n]]=extraLabel++;
							else{
								typedef std::multimap<uint32_t,uint32_t>::iterator psrc;
								std::pair<psrc, psrc> pos = RNodeIndices.equal_range(community[n]);
								while(pos.first != pos.second){
									if(tmpNodeLabels[pos.first->second] == i){
										tmpNodeLabels[pos.first->second]=extraLabel++;
										break;
									}
									++pos.first;
								}
							}	
						}
					}
                }
            }
            InitializeFromLabelsArray(graph, partition, tmpNodeLabels,NodeIndices,RNodeIndices);	
			*/uint32_t countnum=0;
			extraLabel = partition->m_NumCommunities+1;
			std::vector <uint32_t> tmpNodeLabels(partition->m_NodeLabels);
			for (uint32_t h = 0; h < partition->m_NumCommunities; h++) {
                if (partition->m_CommunityIndices[h] != SCD_INVALID_COMMUNITY) {
                    uint32_t* community = &partition->m_Communities[partition->m_CommunityIndices[h] + 1];
                    uint32_t communitySize = partition->m_Communities[partition->m_CommunityIndices[h]];

//					uint32_t d[500][500];
//					memset(d,0,sizeof(d));
					typedef std::set<uint32_t> neighbor;
					neighbor *d = new neighbor[communitySize];
					
					for (uint32_t i = 0; i < communitySize; i++){
						const uint32_t* adjacencies1 = graph->GetNeighbors(community[i]);
						uint32_t degree1 = graph->GetDegree(community[i]);
						for (uint32_t j = 0; j < communitySize; j++){
							if (i == j){
//								d[i][j] = 1;
								d[i].insert(j);
								continue;
							}
							uint32_t*  currentNode1     = (uint32_t*) adjacencies1;
							uint32_t*  endAdjacencies1  = (uint32_t*) adjacencies1 + degree1;
							while (currentNode1 != endAdjacencies1){
                                if(*currentNode1==community[j]){
//									d[i][j] = 1;
									d[i].insert(j);
									break;
								}
                                currentNode1++;
                            }
						}
					}
			
					std::vector<uint32_t> mark(communitySize,0);
					std::queue<uint32_t> q;
					q.push(0);
					uint32_t conn_num = 0;
					mark[0] = 1;
					while (!q.empty()){
						uint32_t t = q.front();
						q.pop();
						conn_num++;
						for (uint32_t i = 0; i < communitySize; i++)
//							if (d[t][i] == 1 && mark[i] == 0){
							if(d[t].find(i)!=d[t].end() && mark[i]==0){
								q.push(i);
								mark[i] = 1;
							}
					}
	
					if (conn_num != communitySize){
						for(uint32_t n = 0; n < communitySize; n++){
							if(tmpNodeLabels[community[n]]==h)
								tmpNodeLabels[community[n]]=extraLabel++;
							else{
								typedef std::multimap<uint32_t,uint32_t>::iterator psrc;
								std::pair<psrc, psrc> pos = RNodeIndices.equal_range(community[n]);
								while(pos.first != pos.second){
									if(tmpNodeLabels[pos.first->second] == h){
										tmpNodeLabels[pos.first->second]=extraLabel++;
										break;
									}
									++pos.first;
								}
							}	
						}
						countnum++;
					}
				}
			}
			printf("delete disconnected community number:%d\n",countnum);
			InitializeFromLabelsArray(graph, partition, tmpNodeLabels,NodeIndices,RNodeIndices);
            return 1;
        }
        return 0;
    }

    static Movement OnlyInsertNode(const CGraph* graph, uint32_t node, CommunityPartition* partition,
                                         std::map<uint32_t, uint32_t>&NodeIndices,
										 std::multimap<uint32_t, uint32_t>&RNodeIndices,uint32_t semiTriangle,
										 const std::vector<uint32_t>&tempNodeLabels,
										 uint32_t N) {

        Movement movement;
        movement.m_MovementType = E_NO_MOVEMENT;
        movement.m_NodeId       = node;

        std::map<uint32_t, uint32_t> neighborsCommunity;
        neighborsCommunity.insert(std::pair<uint32_t, uint32_t>(tempNodeLabels[node], 0));
        const uint32_t * adjacencies ;
        uint32_t degree ;

        if(node < graph->GetNumNodes()){
            adjacencies = graph->GetNeighbors(node);
            degree = graph->GetDegree(node);   
        }
        else{
            adjacencies = graph->GetNeighbors((*NodeIndices.find(node)).second);
            degree = graph->GetDegree((*NodeIndices.find(node)).second);   
        }

		for (uint32_t i = 0; i < degree; i++) {
            uint32_t neighbor = adjacencies[i];
            if (partition->m_Communities[partition->m_CommunityIndices[tempNodeLabels[neighbor]]] > 1) {
                std::map<uint32_t, uint32_t>::iterator it = neighborsCommunity.find(tempNodeLabels[neighbor]);
                if (it != neighborsCommunity.end()) {
                    (*it).second++;
                } else {
                    neighborsCommunity.insert(std::pair<uint32_t, uint32_t>(tempNodeLabels[neighbor], 1));
                }
            }
			typedef std::multimap<uint32_t,uint32_t>::iterator psrc;
			std::pair<psrc, psrc> pos = RNodeIndices.equal_range(neighbor);
			while(pos.first != pos.second){
				if(pos.first->second < N){
				if( partition->m_Communities[partition->m_CommunityIndices[tempNodeLabels[pos.first->second]]] > 1){			
					std::map<uint32_t, uint32_t>::iterator it = neighborsCommunity.find(tempNodeLabels[pos.first->second]);
					if (it != neighborsCommunity.end()) {
						(*it).second++;
					} else {
						neighborsCommunity.insert(std::pair<uint32_t, uint32_t>(tempNodeLabels[pos.first->second], 1));
					}
				}
				}
				++pos.first;
			}
        }

        bool removeCommunity = false;
        uint32_t bestRemoveInternalEdges = 0;
        uint32_t auxInternalEdges = (*neighborsCommunity.find(tempNodeLabels[node])).second;
        uint32_t community = tempNodeLabels[node];
        uint32_t communityIndex = partition->m_CommunityIndices[community];
        uint32_t communitySize = partition->m_Communities[communityIndex];
        double64_t p_in;
        if ((communitySize - 2) != 0 && (communitySize - 1) != 0) {
			p_in = (partition->m_InternalEdges[community] - auxInternalEdges * 2) / ((double64_t) (communitySize - 1) * (communitySize - 2));
		} else {
            p_in = 0.0f;
        }
        double64_t p_ext = graph->GetCC();
        double64_t p_ext_node = p_ext;
        double64_t bestRemoveImprovement;
        bestRemoveImprovement = -CheckForIncrement(communitySize - 1, auxInternalEdges,
                degree - auxInternalEdges,
                partition->m_ExternalEdges[community]/2 + auxInternalEdges - (degree - auxInternalEdges),
                p_ext_node, p_in, p_ext,graph->GetEdgesProbablity(),semiTriangle);
        bestRemoveInternalEdges = auxInternalEdges;
 
		if(communitySize==1)
			removeCommunity = true;

        uint32_t   bestInsertCommunity;
        double64_t bestInsertImprovement      = -10000000000000.0;		
        uint32_t   bestInsertInternalEdges    = 0;
		bool       copyCommunity              = false;
		bool       insertCommunity              = false;
        for (std::map<uint32_t, uint32_t>::iterator it = neighborsCommunity.begin(); it != neighborsCommunity.end(); ++it) {
            uint32_t community = it->first;
            if (community != tempNodeLabels[node]) {
                uint32_t auxInternalEdges = it->second;
                uint32_t communityIndex   = partition->m_CommunityIndices[community];
                uint32_t communitySize    = partition->m_Communities[communityIndex];
                double64_t p_in;
                if ((communitySize - 1) > 0 && (communitySize > 0)) {
                p_in = (partition->m_InternalEdges[community]) / ((double64_t) (communitySize) * (communitySize - 1));
				} else {
                    p_in = 0.0;
                }

                double64_t p_ext          = graph->GetCC();
                double64_t p_ext_node     = p_ext;
                double64_t auxImprovement = CheckForIncrement(communitySize, auxInternalEdges, degree - auxInternalEdges,
                        partition->m_ExternalEdges[community]/2, p_ext_node, p_in, p_ext,graph->GetEdgesProbablity(),semiTriangle);
				if(removeCommunity){
					if (auxImprovement>0 && auxImprovement + bestRemoveImprovement > bestInsertImprovement) {
						insertCommunity = true;
						bestInsertImprovement = auxImprovement + bestRemoveImprovement;
						bestInsertCommunity = community;
						bestInsertInternalEdges = auxInternalEdges;
					}
				}
				else{
					if (auxImprovement>0 && auxImprovement - bestRemoveImprovement > bestInsertImprovement) {
						copyCommunity = true;
						bestInsertImprovement = auxImprovement - bestRemoveImprovement;
						bestInsertCommunity = community;
						bestInsertInternalEdges = auxInternalEdges;
					}
				}
            }
        }

		if(insertCommunity && (partition->m_Communities[partition->m_CommunityIndices[partition->m_NodeLabels[movement.m_NodeId]]] == 1)){
			uint32_t tmp=node;
			if(node >= graph->GetNumNodes()){
				node=(*NodeIndices.find(node)).second;
			}
			if( partition->m_NodeLabels[node]== bestInsertCommunity ){
				if(partition->m_Communities[partition->m_CommunityIndices[partition->m_NodeLabels[movement.m_NodeId]]] == 1)
					return movement;
				movement.m_MovementType =E_REMOVE;
				return movement;
			}
			typedef std::multimap<uint32_t,uint32_t>::iterator psrc;
			std::pair<psrc, psrc> pos = RNodeIndices.equal_range(node);
			uint32_t c = RNodeIndices.count(node);
			while(pos.first != pos.second){
				if( partition->m_NodeLabels[pos.first->second]== bestInsertCommunity ){			
					if(partition->m_Communities[partition->m_CommunityIndices[partition->m_NodeLabels[movement.m_NodeId]]] == 1)
						return movement;
					movement.m_MovementType =E_REMOVE;
					return movement;
				}
				++pos.first;
			}

            movement.m_MovementType = E_REMOVE_AND_INSERT;
            movement.m_Community = bestInsertCommunity;
			partition->m_NodeLabels[tmp]=bestInsertCommunity;	
        }
		else if(copyCommunity){	
			if(node >= graph->GetNumNodes()){
				node=(*NodeIndices.find(node)).second;
			}
			if( partition->m_NodeLabels[node]== bestInsertCommunity ){
				return movement;
			}
			typedef std::multimap<uint32_t,uint32_t>::iterator psrc;
			std::pair<psrc, psrc> pos = RNodeIndices.equal_range(node);
			uint32_t c = RNodeIndices.count(node);
			while(pos.first != pos.second){
				if( partition->m_NodeLabels[pos.first->second]== bestInsertCommunity )
					return movement;
				++pos.first;
			}
			if( NodeIndices.size()==0 )
				movement.m_NodeId = graph->GetNumNodes();
			else{
				std::map<uint32_t,uint32_t>::iterator it;
				it = NodeIndices.end();
				it--;
				movement.m_NodeId = it->first + 1 ;
			}
            NodeIndices.insert(std::pair<uint32_t, uint32_t>(movement.m_NodeId, node));
			RNodeIndices.insert(std::pair<uint32_t,uint32_t>(node, movement.m_NodeId));
			partition->m_NodeLabels.push_back(bestInsertCommunity);

			movement.m_src = node;
            movement.m_MovementType = E_COPY;
            movement.m_Community = bestInsertCommunity;
        }
		else if(removeCommunity){
			if(partition->m_Communities[partition->m_CommunityIndices[partition->m_NodeLabels[movement.m_NodeId]]] == 1)
				return movement;
			else
				printf("error happen in last step remove community\n");
		}
        return movement;
    }
	
      static uint32_t LastStepToKillIsolate(const CGraph* graph, CommunityPartition* partition,
                                           std::map<uint32_t,uint32_t>& NodeIndices,
                                           std::multimap <uint32_t, uint32_t> &RNodeIndices,uint32_t semiTriangle) {
        std::vector<Movement>* movements = new std::vector<Movement>[num_threads];
        uint32_t N = graph->GetNumNodes()+NodeIndices.size();  
	
        std::vector <uint32_t> tempNodeLabels(partition->m_NodeLabels);
        uint32_t noMovements = 0;
        //only single nodes can be inserted into the best community.
		//all nodes can be copied to the best community.
		//no nodes can be removed from the community.
        for (uint32_t i = 0; i < N; i++) {
            int thread = omp_get_thread_num();
            if (i % 100000 == 0) {
                printf("Checked movements of %d nodes.", i);
				printf("\r");
            }
            Movement movement; 
            movement = OnlyInsertNode(graph, i, partition,NodeIndices,RNodeIndices,semiTriangle,tempNodeLabels,N);
            if(movement.m_MovementType == E_REMOVE_AND_INSERT || movement.m_MovementType == E_COPY)
				movements[thread].push_back(movement);
            else
                noMovements++;
        }

        printf("All movements checked\n");

        uint32_t totalMovements = 0;
        uint32_t removeMovements = 0;
        uint32_t removeAndInsertMovements = 0;
        uint32_t insertMovements = 0;
        uint32_t copyMovements = 0;    
        uint32_t extraLabel;
#pragma omp parallel for schedule(static,1)   
        for (uint32_t thread = 0; thread < num_threads; thread++) {
            uint32_t numMovements = movements[thread].size();
            totalMovements += numMovements;
            uint32_t nextLabelThread = partition->m_NumCommunities + numMovements * thread;   

            for (uint32_t i = 0; i < numMovements; i++) {
                Movement movement = (movements[thread])[i];
                switch (movement.m_MovementType) {
                    case E_REMOVE_AND_INSERT:
                        if (partition->m_Communities[partition->m_CommunityIndices[tempNodeLabels[movement.m_NodeId]]] == 1) {
                            insertMovements++;
                        } else {
                            removeAndInsertMovements++;
                        }
                        tempNodeLabels[movement.m_NodeId] = movement.m_Community;
                        break;
                    case E_COPY:
                        tempNodeLabels.push_back(movement.m_Community);
                        copyMovements++;
                        break;
                }
            }
        }
        delete [] movements;
        printf(" Last Step: Number of removes performed: %d\n", removeMovements);
        printf(" Last Step: Number of remove and insert performed: %d\n", removeAndInsertMovements);
        printf(" Last Step: Number of insert performed: %d\n", insertMovements);
        printf(" Last Step: Number of copy performed: %d\n", copyMovements);
        printf(" Last Step: Number of nothing performed: %d\n", noMovements);      
        FreeResources(partition);
        
        if (InitializeFromLabelsArray(graph, partition, tempNodeLabels,NodeIndices,RNodeIndices)) {
            printf("Error initializing from label array.\n");
            return 1;
        }	
    return 0;        
    }


    /** @brief Measures the memory consumption of a partition.
      @param partition The partition to measure.
      @return The size in bytes of the structure.*/
    static uint64_t MeasureMemoryConsumption(const CommunityPartition* partition) {
        uint64_t memoryConsumption = 0;
        memoryConsumption += sizeof (uint32_t)  * partition->m_NumNodes; //Labels array consumption.
        memoryConsumption += sizeof (uint32_t)  * partition->m_NumCommunities; //Community indices consumption.
        memoryConsumption += sizeof (uint32_t)  *(partition->m_NumCommunities + partition->m_NumNodes); //Communities consumption.
        memoryConsumption += sizeof (uint32_t)  * partition->m_NumCommunities; //Internal edges consumption.
        memoryConsumption += sizeof (uint32_t)  * partition->m_NumCommunities; //External edges consumption.
        memoryConsumption += sizeof (double64_t)* partition->m_NumNodes; //WCCs consumption.
        memoryConsumption += sizeof (uint32_t); //NumNodes consumption.
        memoryConsumption += sizeof (uint32_t); //NumCommunities consumption.
        memoryConsumption += sizeof (double64_t); //WCC consumption.
        return memoryConsumption;
    }

    uint32_t    LoadPartition( const CGraph* graph, CommunityPartition* partition, const char_t* partitionFileName ) {

        std::map<uint32_t, uint32_t> oldToNew;
        const uint32_t* newToOld = graph->GetMap();
        for( uint32_t i = 0; i < graph->GetNumNodes(); ++i ) {
            oldToNew.insert(std::pair<uint32_t, uint32_t>(newToOld[i],i));
        }
		std::vector<uint32_t> Vcommunities;
        uint32_t* communities = new uint32_t[graph->GetNumNodes()];
        memset(communities,0xff,sizeof(uint32_t)*graph->GetNumNodes());
        if (!communities) {
            printf("Unable to allocate partition\n");
            return 1;
        }

        std::ifstream partitionFile;
        partitionFile.open(partitionFileName);
        if(!partitionFile.is_open()) {
            printf("Unable to load partition file.\n");
            return 1;
        }
        std::string line;
        uint32_t nextLabel = 0;
        while(std::getline(partitionFile,line)) {
            std::istringstream stream(line);
            uint32_t node;
            while( stream >> node ) {
                communities[oldToNew[node]] = nextLabel;
            }
            ++nextLabel;
        }
        for( uint32_t i=0; i<graph->GetNumNodes(); ++i) {
            if( communities[i] == 0xffffffff ) {
                communities[i] = nextLabel++;
            }
        }
        partitionFile.close();
		for(uint32_t i = 0; i < graph->GetNumNodes(); i++)//communities转换为vector型的Vcommunities
			Vcommunities.push_back(communities[i]);
		std::map<uint32_t,uint32_t> tmp1;
		std::multimap<uint32_t,uint32_t> tmp2;		
        InitializeFromLabelsArray(graph,partition,Vcommunities,tmp1,tmp2);
        delete [] communities;
        return 0;
    }

    uint32_t InitializeSimplePartition(const CGraph* graph, CommunityPartition* partition) {
        //Computing the clustering coefficient of each node of the graph.
		std::vector<uint32_t> Vcommunities;
        NodeClustering* nC = new NodeClustering[graph->GetNumNodes()];
        if (!nC) {
            printf("Error allocating node clustering array.");
            return 1;
        }
        for (uint32_t i = 0; i < graph->GetNumNodes(); i++) {
            nC[i].m_NodeId = i;
            nC[i].m_Degree = graph->GetDegree(i);
            nC[i].m_CC = graph->GetTotalTriangles(i) / (double64_t) (nC[i].m_Degree * (nC[i].m_Degree - 1));
        }
        qsort(nC, graph->GetNumNodes(), sizeof (NodeClustering), Compare_NodeClusterings);
        //Creating a vector to track which nodes have already been visited.
        bool * visited = new bool[graph->GetNumNodes()];
        if (!visited) {
            printf("Error allocating visited array.");
            return 1;
        }
		
        memset(visited, false, graph->GetNumNodes() );
        uint32_t* communities = new uint32_t[graph->GetNumNodes()];
        if (!communities) {
            printf("Error allocating communities array.\n");
            return 1;
        }
	
        uint32_t nextLabel = 0;
        for (uint32_t i = 0; i < graph->GetNumNodes(); i++) {
            NodeClustering* nodeClustering = &nC[i];
            if (!visited[nodeClustering->m_NodeId]) {
                visited[nodeClustering->m_NodeId] = true;
                communities[nodeClustering->m_NodeId] = nextLabel;
                const uint32_t* adjacencies1= graph->GetNeighbors(nodeClustering->m_NodeId);
                uint32_t degree=graph->GetDegree(nodeClustering->m_NodeId);

				
                for (uint32_t j = 0; j < degree; j++) {
                    if (!visited[adjacencies1[j]]) {                        
                        visited[adjacencies1[j]] = true;
                        communities[adjacencies1[j]] = nextLabel;                       
                    }
                }
                nextLabel++;
            }
        }
        delete [] visited;
        delete [] nC;
		
		for(uint32_t i = 0; i < graph->GetNumNodes(); i++)
			Vcommunities.push_back(communities[i]);
		std::map<uint32_t,uint32_t> tmp1;
		std::multimap<uint32_t,uint32_t> tmp2;		
        InitializeFromLabelsArray(graph, partition, Vcommunities,tmp1,tmp2);
        delete [] communities;
        return 0;
    }

    uint32_t CopyPartition(CommunityPartition* destPartition, const CommunityPartition* sourcePartition) {

        destPartition->m_CommunityIndices = new uint32_t[sourcePartition->m_NumCommunities];
        if (!destPartition->m_CommunityIndices) {
            printf("Error while allocating community indices.\n");
            return 1;
        }

        destPartition->m_Communities = new uint32_t[sourcePartition->m_NumCommunities + sourcePartition->m_NumNodes];
        if (!destPartition->m_Communities) {
            printf("Error while allocating communities.\n");
            return 1;
        }

        destPartition->m_InternalEdges = new uint32_t[sourcePartition->m_NumCommunities];
        if (!destPartition->m_InternalEdges) {
            printf("Error while allocating InternalEdges.\n");
            return 1;
        }

        destPartition->m_ExternalEdges = new uint32_t[sourcePartition->m_NumCommunities];
        if (!destPartition->m_ExternalEdges) {
            printf("Error while allocating InternalEdges.\n");
            return 1;
        }

        destPartition->m_NodeWCC = new double64_t[sourcePartition->m_NumNodes];
        if (!destPartition->m_NodeWCC) {
            printf("Error while allocating WCCs.\n");
            return 1;
        }

		destPartition->m_NodeLabels=sourcePartition->m_NodeLabels;
        memcpy(destPartition->m_CommunityIndices, sourcePartition->m_CommunityIndices, sizeof (uint32_t)*(sourcePartition->m_NumCommunities));
        memcpy(destPartition->m_Communities, sourcePartition->m_Communities, sizeof (uint32_t)*(sourcePartition->m_NumCommunities + sourcePartition->m_NumNodes));
        memcpy(destPartition->m_InternalEdges, sourcePartition->m_InternalEdges, sizeof (uint32_t)*(sourcePartition->m_NumCommunities));
        memcpy(destPartition->m_ExternalEdges, sourcePartition->m_ExternalEdges, sizeof (uint32_t)*(sourcePartition->m_NumCommunities));
        memcpy(destPartition->m_NodeWCC, sourcePartition->m_NodeWCC, sizeof (double64_t)*(sourcePartition->m_NumNodes));
        destPartition->m_NumNodes = sourcePartition->m_NumNodes;
        destPartition->m_NumCommunities = sourcePartition->m_NumCommunities;
        destPartition->m_WCC = sourcePartition->m_WCC;
        return 0;
    }


    uint32_t PrintPartition(const CGraph* graph, const CommunityPartition* partition, const char_t* fileName) {

        std::ofstream outFile;
        outFile.open(fileName);
		uint32_t size=0;
		uint32_t size_num=0;
		uint32_t countnum=0;
		const uint32_t* adjacencies1;
		const uint32_t* adjacencies2;
        uint32_t        degree1,degree2;
        for (uint32_t i = 0; i < partition->m_NumCommunities; i++) {
            if (partition->m_CommunityIndices[i] != SCD_INVALID_COMMUNITY) {
                uint32_t* community = &partition->m_Communities[partition->m_CommunityIndices[i] + 1];
                uint32_t communitySize = partition->m_Communities[partition->m_CommunityIndices[i]];
				uint32_t flag=0;
				if(communitySize<3)
					continue;
					
				for (uint32_t j = 0; j < communitySize; j++) {
                    adjacencies1 = graph->GetNeighbors(community[j]);
                    degree1 = graph->GetDegree(community[j]);   
                    for (uint32_t k = 0; k < communitySize; k++) {  
						if(j==k)
							continue;
                        uint32_t*  currentNode1     = (uint32_t*) adjacencies1;
                        uint32_t*  endAdjacencies1  = (uint32_t*) adjacencies1 + degree1;
            
                        while (currentNode1 != endAdjacencies1){
                            if(*currentNode1==community[k]){
                                flag++;
								break;
							}
                            currentNode1++;
                        }                     
                    }	
                }
                if(flag/2<communitySize){
					countnum++;
					continue;
				}

                for (uint32_t j = 0; j < communitySize - 1; j++) {
                    outFile << graph->ReMap(community[j]) << " ";
					
				}
                outFile << graph->ReMap(community[communitySize - 1]) << std::endl;
				size+=communitySize;
				size_num++;
				
            }
        }
		printf("delete:%d\n",countnum);
		printf("community node/node:%lf\n",(double64_t)size/(double64_t)graph->GetNumNodes());
		printf("the average community size is %lf\n",(double64_t)size/(double64_t)size_num);
        outFile.close();
        return 0;
    }


    void FreeResources(CommunityPartition* partition) {
        if (partition->m_CommunityIndices != NULL) {
            delete [] partition->m_CommunityIndices;
            partition->m_CommunityIndices = NULL;
        }

        if (partition->m_Communities != NULL) {
            delete [] partition->m_Communities;
            partition->m_Communities = NULL;
        }

        if (partition->m_InternalEdges != NULL) {
            delete [] partition->m_InternalEdges;
            partition->m_InternalEdges = NULL;
        }

        if (partition->m_ExternalEdges != NULL) {
            delete [] partition->m_ExternalEdges;
            partition->m_ExternalEdges = NULL;
        }

        if (partition->m_NodeWCC != NULL) {
            delete [] partition->m_NodeWCC;
            partition->m_NodeWCC = NULL;
        }
        partition->m_NumCommunities = 0;
        partition->m_NumNodes = 0;
        partition->m_WCC = 0.0;
    }


    uint32_t ImproveCommunities(const CGraph* graph, CommunityPartition* partition, uint32_t numThreads, uint32_t semiTriangle ) {
        std::map <uint32_t, uint32_t> NodeIndices;//map<a,b>: Node a is a copy of node b
		std::multimap <uint32_t, uint32_t> RNodeIndices;//multimap<a,b>: Node b is a copy of node a
        num_threads = numThreads;
        omp_set_num_threads(num_threads);
        printf("Maximum number of threads: %d\n", omp_get_max_threads());
        printf("Starting improvement from a partition with WCC: %f\n", partition->m_WCC / graph->GetNumNodes());
        CommunityPartition bestPartition;
        CopyPartition(&bestPartition, partition);

        bool improve = true;

        while (improve) {
            printf("\n");
            uint64_t initTime = StartClock();

            printf("Starting improvement iteration ...\n");
            if (PerformImprovementStep(graph, partition,NodeIndices,RNodeIndices,semiTriangle)) {
                printf("Finish or error while performing an improvement step.\n");
                printf("Last Step To Kill Isolate Nodes.\n");
                LastStepToKillIsolate(graph, partition,NodeIndices,RNodeIndices,semiTriangle);
				improve = false;
            }
			FreeResources(&bestPartition);
			CopyPartition(&bestPartition, partition);      
			printf("Memory required by this iteration: %lu bytes \n", MeasureMemoryConsumption(partition) + MeasureMemoryConsumption(&bestPartition));

            printf("Iteration time: %lu ms\n", StopClock(initTime));

		}

        FreeResources(partition);
        CopyPartition(partition, &bestPartition);
        FreeResources(&bestPartition);
        return 0;
    }
}

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

#include <wcc/wcc.h>
#include <omp.h>
#include <communities/communities.h>

namespace scd {

    
    uint32_t Intersect(/*const*/ uint32_t* list1, const uint32_t size1, /*const*/ uint32_t* list2, const uint32_t size2) {
        uint32_t triangles = 0;

        uint32_t* endList1 = list1 + size1;
        uint32_t* endList2 = list2 + size2;


        // v2.0
        while (list1 != endList1 && list2 != endList2) {
            if (*list1 < *list2) {
                list1++;                
            } else if (*list1 > *list2) {
                list2++;                
            } else { //(*list1 == *list2){ //triangle found
                triangles++;
                list1++;
                list2++;
            }
        }

        return triangles;
    }
    
    
    
// ComputeWCC(graph, partition->m_NodeLabels,
//            partition->m_NumCommunities, partition->m_CommunityIndices, 
//            partition->m_Communities, partition->m_NodeWCC);
    
    double64_t ComputeWCC(const CGraph * graph, std::vector <uint32_t>& communities, 
            const uint32_t numCommunities, const uint32_t* labelsIndices, 
            const uint32_t * communitiesInvIndex, double64_t* wccs,std::map<uint32_t,uint32_t>& NodeIndices,
			std::multimap<uint32_t,uint32_t>& RNodeIndices,double64_t* CommunityCopySize) {    
        double64_t globalWCC = 0;
        
        #pragma omp parallel for schedule(static, 8) reduction(+:globalWCC)
        for (uint32_t i = 0; i < graph->GetNumNodes(); i++) {
//            uint32_t communitySize = communitiesInvIndex[labelsIndices[communities[i]]];
			double64_t communitySize=0;
			std::vector <uint32_t> communityLabel;
			typedef std::multimap<uint32_t,uint32_t>::iterator psrc;
			std::pair<psrc, psrc> pos = RNodeIndices.equal_range(i);
			uint32_t c = RNodeIndices.count(i);
			while(pos.first != pos.second){
				communitySize+=CommunityCopySize[communities[pos.first->second]];
				communityLabel.push_back(communities[pos.first->second]);
				pos.first++;
			}
				
            wccs[i] = ComputeWCC(graph, i, communityLabel, communities, communitySize, NodeIndices);
            globalWCC += wccs[i];
        }
        return globalWCC;
    }

    
    double64_t ComputeWCC(const CGraph * graph, uint32_t node, std::vector <uint32_t>&communityLabel, 
            std::vector <uint32_t>&communities, double64_t communitySize, std::map<uint32_t,uint32_t>& NodeIndices) {
        
        uint32_t        internalTriangles      = 0;
        uint32_t        internalTriangleDegree = 0;
        uint32_t        triangleDegree         = 0;
        uint32_t        node1                  = node;
        const uint32_t* adjacencies1;
        uint32_t        degree1;
        
        if(node < graph->GetNumNodes()){//新增点和原有点分别对待
            adjacencies1 = graph->GetNeighbors(node1);
            degree1 = graph->GetDegree(node1);   
        }
        else{
            adjacencies1 = graph->GetNeighbors((*NodeIndices.find(node)).second);
            degree1 = graph->GetDegree((*NodeIndices.find(node)).second);   
        }

        if(node < graph->GetNumNodes()){
           if (communitySize <= 2 ||graph->GetTotalTriangles(node) == 0) {
                return 0.0;
            }
        }
        else
            if (communitySize <= 2 ||graph->GetTotalTriangles((*NodeIndices.find(node)).second) == 0) 
                return 0.0;
        
		for(uint32_t cl; cl<communityLabel.size(); cl++){
        //while(adjacencies1 < endList1){
			for (uint32_t k = 0; k < degree1; k++) {
				uint32_t        nodeId2  = adjacencies1[k];
				uint32_t        degree2  = graph->GetDegree(nodeId2);                        
				bool            internal = (communities[nodeId2] == communityLabel[cl]);
				bool            internalTriangleFound = false;
				bool            triangleFound         = false;
				const uint32_t* adjacencies2;
            
				if(nodeId2 < graph->GetNumNodes())
					adjacencies2=graph->GetNeighbors(nodeId2);
				else
					adjacencies2=graph->GetNeighbors((*NodeIndices.find(nodeId2)).second);
			
				uint32_t*  currentNode1     = (uint32_t*) adjacencies1;
				uint32_t*  currentNode2     = (uint32_t*) adjacencies2;
				uint32_t*  endAdjacencies1  = (uint32_t*) adjacencies1 + degree1;
				uint32_t*  endAdjacencies2  = (uint32_t*) adjacencies2 + degree2;
            
				while (currentNode1 != endAdjacencies1 && currentNode2 != endAdjacencies2){
					if (*currentNode1 == *currentNode2){
						uint32_t sharedNeighbor = *currentNode1;
						if (internal && communities[sharedNeighbor] == communityLabel[cl]) {
							internalTriangleFound = true;
							internalTriangles++;
						}
						triangleFound = true;
						currentNode1++;
						currentNode2++;
					}else  if(*currentNode1 < *currentNode2){
						while(*currentNode1 < *currentNode2 && currentNode1 < endAdjacencies1){
							currentNode1++;
						}
					}else{
						while(*currentNode1 > *currentNode2 && currentNode2 < endAdjacencies2){
							currentNode2++;
						}
					}
				}
            
				if (internalTriangleFound) {
					internalTriangleDegree++;
				}
				if (triangleFound) {
					triangleDegree++;
				}
			}
        }
		 if(node < graph->GetNumNodes()){
			return ((internalTriangles / (double64_t) graph->GetTotalTriangles(node)) *
               (triangleDegree / (double64_t) (triangleDegree - internalTriangleDegree + communitySize - 1)));
        }
		else
			 return ((internalTriangles / (double64_t) graph->GetTotalTriangles((*NodeIndices.find(node)).second)) *
               (triangleDegree / (double64_t) (triangleDegree - internalTriangleDegree + communitySize - 1)));

/* if(node < graph->GetNumNodes()){
			return (internalTriangles / (double64_t) graph->GetTotalTriangles(node));
        }
		else
			 return (internalTriangles / (double64_t) graph->GetTotalTriangles((*NodeIndices.find(node)).second));
*/		
       
    }
}



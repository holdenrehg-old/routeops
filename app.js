(function e(t,n,r){function s(o,u){if(!n[o]){if(!t[o]){var a=typeof require=="function"&&require;if(!u&&a)return a(o,!0);if(i)return i(o,!0);throw new Error("Cannot find module '"+o+"'")}var f=n[o]={exports:{}};t[o][0].call(f.exports,function(e){var n=t[o][1][e];return s(n?n:e)},f,f.exports,e,t,n,r)}return n[o].exports}var i=typeof require=="function"&&require;for(var o=0;o<r.length;o++)s(r[o]);return s})({1:[function(require,module,exports){
/*
  This encapsulates reusable functionality for resolving TSP problems on
  Google Maps.
  The authors of this code are James Tolley <info [at] gmaptools.com>
  and Geir K. Engdahl <geir.engdahl (at) gmail.com>

  For the most up-to-date version of this file, see
  http://code.google.com/p/google-maps-tsp-solver/

  To receive updates, subscribe to google-maps-tsp-solver@googlegroups.com

  version 1.0; 05/07/10

  // Usage:
  See http://code.google.com/p/google-maps-tsp-solver/
*/

(function(logger) {
    var tsp; // singleton
    var gebMap; // The map DOM object
    var directionsPanel; // The driving directions DOM object
    var gebDirectionsResult; // The driving directions returned from GMAP API
    var gebDirectionsService;
    var gebGeocoder; // The geocoder for addresses
    var maxTspSize = 1000000; // A limit on the size of the problem, mostly to save Google servers from undue load.
    var maxTspBF = 0; // Max size for brute force, may seem conservative, but ma
    var maxTspDynamic = 15; // Max size for brute force, may seem conservative, but many browsers have limitations on run-time.
    var maxSize = 10; // Max number of waypoints in one Google driving directions request.
    var maxTripSentry = 2000000000; // Approx. 63 years., this long a route should not be reached...
    var avoidHighways = false; // Whether to avoid highways. False by default.
    var avoidTolls = false; // Whether to avoid toll roads. False by default.
    var travelMode;
    var distIndex;
    var waypoints = new Array();
    var addresses = new Array();
    var GEO_STATUS_MSG = new Array();
    var DIR_STATUS_MSG = new Array();
    var labels = new Array();
    var addr = new Array();
    var wpActive = new Array();
    var addressRequests = 0;
    var addressProcessing = false;
    var requestNum = 0;
    var totalRequests = 0;
    var currQueueNum = 0;
    var wayArr;
    var legsTmp;
    var distances;
    var durations;
    var legs;
    var dist;
    var dur;
    var visited;
    var currPath;
    var bestPath;
    var bestTrip;
    var nextSet;
    var numActive;
    var costForward;
    var costBackward;
    var improved = false;
    var chunkNode;
    var okChunkNode;
    var numDirectionsComputed = 0;
    var numDirectionsNeeded = 0;
    var cachedDirections = false;
    var requestLimitWait = 1000;
    var fakeDirResult; // Object used to store travel info like travel mode etc. Needed for route renderer.
    var currentPercentage = 0; // percentage done calculating

    var onSolveCallback = function() {};
    var onProgressCallback = null;
    var originalOnFatalErrorCallback = function(tsp, errMsg) {
        alert("Request failed: " + errMsg);
    }
    var onFatalErrorCallback = originalOnFatalErrorCallback;
    var doNotContinue = false;
    var onLoadListener = null;
    var onFatalErrorListener = null;

    var directionunits;

    /** Computes greedy (nearest-neighbor solution to the TSP)
     */
    function tspGreedy(mode) {
        var curr = 0;
        var currDist = 0;
        var numSteps = numActive - 1;
        var lastNode = 0;
        var numToVisit = numActive;
        if (mode == 1) {
            numSteps = numActive - 2;
            lastNode = numActive - 1;
            numToVisit = numActive - 1;
        }
        for (var step = 0; step < numSteps; ++step) {
            visited[curr] = true;
            bestPath[step] = curr;
            var nearest = maxTripSentry;
            var nearI = -1;
            for (var next = 1; next < numToVisit; ++next) {
                if (!visited[next] && dur[curr][next] < nearest) {
                    nearest = dur[curr][next];
                    nearI = next;
                }
            }
            currDist += dur[curr][nearI];
            curr = nearI;
        }
        if (mode == 1) bestPath[numSteps] = lastNode;
        else bestPath[numSteps] = curr;
        currDist += dur[curr][lastNode];
        bestTrip = currDist;
    }

    /** Returns the cost of moving along the current solution path offset
     *  given by a to b. Handles moving both forward and backward.
     */
    function cost(a, b) {
        if (a <= b) {
            return costForward[b] - costForward[a];
        } else {
            return costBackward[b] - costBackward[a];
        }
    }

    /** Returns the cost of the given 3-opt variation of the current solution.
     */
    function costPerm(a, b, c, d, e, f) {
        var A = currPath[a];
        var B = currPath[b];
        var C = currPath[c];
        var D = currPath[d];
        var E = currPath[e];
        var F = currPath[f];
        var g = currPath.length - 1;

        var ret = cost(0, a) + dur[A][B] + cost(b, c) + dur[C][D] + cost(d, e) + dur[E][F] + cost(f, g);
        return ret;
    }

    /** Update the datastructures necessary for cost(a,b) and costPerm to work
     *  efficiently.
     */
    function updateCosts() {
        costForward = new Array(currPath.length);
        costBackward = new Array(currPath.length);

        costForward[0] = 0.0;
        for (var i = 1; i < currPath.length; ++i) {
            costForward[i] = costForward[i - 1] + dur[currPath[i - 1]][currPath[i]];
        }
        bestTrip = costForward[currPath.length - 1];

        costBackward[currPath.length - 1] = 0.0;
        for (var i = currPath.length - 2; i >= 0; --i) {
            costBackward[i] = costBackward[i + 1] + dur[currPath[i + 1]][currPath[i]];
        }
    }

    /** Update the current solution with the given 3-opt move.
     */
    function updatePerm(a, b, c, d, e, f) {
        improved = true;
        var nextPath = new Array(currPath.length);
        for (var i = 0; i < currPath.length; ++i) nextPath[i] = currPath[i];
        var offset = a + 1;
        nextPath[offset++] = currPath[b];
        if (b < c) {
            for (var i = b + 1; i <= c; ++i) {
                nextPath[offset++] = currPath[i];
            }
        } else {
            for (var i = b - 1; i >= c; --i) {
                nextPath[offset++] = currPath[i];
            }
        }
        nextPath[offset++] = currPath[d];
        if (d < e) {
            for (var i = d + 1; i <= e; ++i) {
                nextPath[offset++] = currPath[i];
            }
        } else {
            for (var i = d - 1; i >= e; --i) {
                nextPath[offset++] = currPath[i];
            }
        }
        nextPath[offset++] = currPath[f];
        currPath = nextPath;

        updateCosts();
    }

    /** Uses the 3-opt algorithm to find a good solution to the TSP.
     */
    function tspK3(mode) {
        // tspGreedy(mode);
        currPath = new Array(bestPath.length);
        for (var i = 0; i < bestPath.length; ++i) currPath[i] = bestPath[i];

        updateCosts();
        improved = true;
        while (improved) {
            improved = false;
            for (var i = 0; i < currPath.length - 3; ++i) {
                for (var j = i + 1; j < currPath.length - 2; ++j) {
                    for (var k = j + 1; k < currPath.length - 1; ++k) {
                        if (costPerm(i, i + 1, j, k, j + 1, k + 1) < bestTrip)
                            updatePerm(i, i + 1, j, k, j + 1, k + 1);
                        if (costPerm(i, j, i + 1, j + 1, k, k + 1) < bestTrip)
                            updatePerm(i, j, i + 1, j + 1, k, k + 1);
                        if (costPerm(i, j, i + 1, k, j + 1, k + 1) < bestTrip)
                            updatePerm(i, j, i + 1, k, j + 1, k + 1);
                        if (costPerm(i, j + 1, k, i + 1, j, k + 1) < bestTrip)
                            updatePerm(i, j + 1, k, i + 1, j, k + 1);
                        if (costPerm(i, j + 1, k, j, i + 1, k + 1) < bestTrip)
                            updatePerm(i, j + 1, k, j, i + 1, k + 1);
                        if (costPerm(i, k, j + 1, i + 1, j, k + 1) < bestTrip)
                            updatePerm(i, k, j + 1, i + 1, j, k + 1);
                        if (costPerm(i, k, j + 1, j, i + 1, k + 1) < bestTrip)
                            updatePerm(i, k, j + 1, j, i + 1, k + 1);
                    }
                }
            }
        }
        for (var i = 0; i < bestPath.length; ++i) bestPath[i] = currPath[i];
    }

    /* Computes a near-optimal solution to the TSP problem, 
     * using Ant Colony Optimization and local optimization
     * in the form of k2-opting each candidate route.
     * Run time is O(numWaves * numAnts * numActive ^ 2) for ACO
     * and O(numWaves * numAnts * numActive ^ 3) for rewiring?
     *
     * if mode is 1, we start at node 0 and end at node numActive-1.
     */
    function tspAntColonyK2(mode) {
        var alfa = 0.1; // The importance of the previous trails
        var beta = 2.0; // The importance of the durations
        var rho = 0.1; // The decay rate of the pheromone trails
        var asymptoteFactor = 0.9; // The sharpness of the reward as the solutions approach the best solution
        var pher = new Array();
        var nextPher = new Array();
        var prob = new Array();
        var numAnts = 20;
        var numWaves = 20;
        for (var i = 0; i < numActive; ++i) {
            pher[i] = new Array();
            nextPher[i] = new Array();
        }
        for (var i = 0; i < numActive; ++i) {
            for (var j = 0; j < numActive; ++j) {
                pher[i][j] = 1;
                nextPher[i][j] = 0.0;
            }
        }

        var lastNode = 0;
        var startNode = 0;
        var numSteps = numActive - 1;
        var numValidDests = numActive;
        if (mode == 1) {
            lastNode = numActive - 1;
            numSteps = numActive - 2;
            numValidDests = numActive - 1;
        }
        for (var wave = 0; wave < numWaves; ++wave) {
            for (var ant = 0; ant < numAnts; ++ant) {
                var curr = startNode;
                var currDist = 0;
                for (var i = 0; i < numActive; ++i) {
                    visited[i] = false;
                }
                currPath[0] = curr;
                for (var step = 0; step < numSteps; ++step) {
                    visited[curr] = true;
                    var cumProb = 0.0;
                    for (var next = 1; next < numValidDests; ++next) {
                        if (!visited[next]) {
                            prob[next] = Math.pow(pher[curr][next], alfa) *
                                Math.pow(dur[curr][next], 0.0 - beta);
                            cumProb += prob[next];
                        }
                    }
                    var guess = Math.random() * cumProb;
                    var nextI = -1;
                    for (var next = 1; next < numValidDests; ++next) {
                        if (!visited[next]) {
                            nextI = next;
                            guess -= prob[next];
                            if (guess < 0) {
                                nextI = next;
                                break;
                            }
                        }
                    }
                    currDist += dur[curr][nextI];
                    currPath[step + 1] = nextI;
                    curr = nextI;
                }
                currPath[numSteps + 1] = lastNode;
                currDist += dur[curr][lastNode];

                // k2-rewire:
                var lastStep = numActive;
                if (mode == 1) {
                    lastStep = numActive - 1;
                }
                var changed = true;
                var i = 0;
                while (changed) {
                    changed = false;
                    for (; i < lastStep - 2 && !changed; ++i) {
                        var cost = dur[currPath[i + 1]][currPath[i + 2]];
                        var revCost = dur[currPath[i + 2]][currPath[i + 1]];
                        var iCost = dur[currPath[i]][currPath[i + 1]];
                        var tmp, nowCost, newCost;
                        for (var j = i + 2; j < lastStep && !changed; ++j) {
                            nowCost = cost + iCost + dur[currPath[j]][currPath[j + 1]];
                            newCost = revCost + dur[currPath[i]][currPath[j]] + dur[currPath[i + 1]][currPath[j + 1]];
                            if (nowCost > newCost) {
                                currDist += newCost - nowCost;
                                // Reverse the detached road segment.
                                for (var k = 0; k < Math.floor((j - i) / 2); ++k) {
                                    tmp = currPath[i + 1 + k];
                                    currPath[i + 1 + k] = currPath[j - k];
                                    currPath[j - k] = tmp;
                                }
                                changed = true;
                                --i;
                            }
                            cost += dur[currPath[j]][currPath[j + 1]];
                            revCost += dur[currPath[j + 1]][currPath[j]];
                        }
                    }
                }

                if (currDist < bestTrip) {
                    bestPath = currPath;
                    bestTrip = currDist;
                }
                for (var i = 0; i <= numSteps; ++i) {
                    nextPher[currPath[i]][currPath[i + 1]] += (bestTrip - asymptoteFactor * bestTrip) / (numAnts * (currDist - asymptoteFactor * bestTrip));
                }
            }
            for (var i = 0; i < numActive; ++i) {
                for (var j = 0; j < numActive; ++j) {
                    pher[i][j] = pher[i][j] * (1.0 - rho) + rho * nextPher[i][j];
                    nextPher[i][j] = 0.0;
                }
            }
        }
    }

    /* Returns the optimal solution to the TSP problem.
     * Run-time is O((numActive-1)!).
     * Prerequisites:
     * - numActive contains the number of locations
     * - dur[i][j] contains weight of edge from node i to node j
     * - visited[i] should be false for all nodes
     * - bestTrip is set to a very high number
     *
     * If mode is 1, it will return the optimal solution to the related
     * problem of finding a path from node 0 to node numActive - 1, visiting
     * the in-between nodes in the best order.
     */
    function tspBruteForce(mode, currNode, currLen, currStep) {
        // Set mode parameters:
        var numSteps = numActive;
        var lastNode = 0;
        var numToVisit = numActive;
        if (mode == 1) {
            numSteps = numActive - 1;
            lastNode = numActive - 1;
            numToVisit = numActive - 1;
        }

        // If this route is promising:
        if (currLen + dur[currNode][lastNode] < bestTrip) {

            // If this is the last node:
            if (currStep == numSteps) {
                currLen += dur[currNode][lastNode];
                currPath[currStep] = lastNode;
                bestTrip = currLen;
                for (var i = 0; i <= numSteps; ++i) {
                    bestPath[i] = currPath[i];
                }
            } else {

                // Try all possible routes:
                for (var i = 1; i < numToVisit; ++i) {
                    if (!visited[i]) {
                        visited[i] = true;
                        currPath[currStep] = i;
                        tspBruteForce(mode, i, currLen + dur[currNode][i], currStep + 1);
                        visited[i] = false;
                    }
                }
            }
        }
    }

    /* Finds the next integer that has num bits set to 1.
     */
    function nextSetOf(num) {
        var count = 0;
        var ret = 0;
        for (var i = 0; i < numActive; ++i) {
            count += nextSet[i];
        }
        if (count < num) {
            for (var i = 0; i < num; ++i) {
                nextSet[i] = 1;
            }
            for (var i = num; i < numActive; ++i) {
                nextSet[i] = 0;
            }
        } else {
            // Find first 1
            var firstOne = -1;
            for (var i = 0; i < numActive; ++i) {
                if (nextSet[i]) {
                    firstOne = i;
                    break;
                }
            }
            // Find first 0 greater than firstOne
            var firstZero = -1;
            for (var i = firstOne + 1; i < numActive; ++i) {
                if (!nextSet[i]) {
                    firstZero = i;
                    break;
                }
            }
            if (firstZero < 0) {
                return -1;
            }
            // Increment the first zero with ones behind it
            nextSet[firstZero] = 1;
            // Set the part behind that one to its lowest possible value
            for (var i = 0; i < firstZero - firstOne - 1; ++i) {
                nextSet[i] = 1;
            }
            for (var i = firstZero - firstOne - 1; i < firstZero; ++i) {
                nextSet[i] = 0;
            }
        }
        // Return the index for this set
        for (var i = 0; i < numActive; ++i) {
            ret += (nextSet[i] << i);
        }
        return ret;
    }

    /* Solves the TSP problem to optimality. Memory requirement is
     * O(numActive * 2^numActive)
     */
    function tspDynamic(mode) {
        var numCombos = 1 << numActive;
        var C = new Array();
        var parent = new Array();
        for (var i = 0; i < numCombos; ++i) {
            C[i] = new Array();
            parent[i] = new Array();
            for (var j = 0; j < numActive; ++j) {
                C[i][j] = 0.0;
                parent[i][j] = 0;
            }
        }
        for (var k = 1; k < numActive; ++k) {
            var index = 1 + (1 << k);
            C[index][k] = dur[0][k];
        }
        for (var s = 3; s <= numActive; ++s) {
            for (var i = 0; i < numActive; ++i) {
                nextSet[i] = 0;
            }
            var index = nextSetOf(s);
            while (index >= 0) {
                for (var k = 1; k < numActive; ++k) {
                    if (nextSet[k]) {
                        var prevIndex = index - (1 << k);
                        C[index][k] = maxTripSentry;
                        for (var m = 1; m < numActive; ++m) {
                            if (nextSet[m] && m != k) {
                                if (C[prevIndex][m] + dur[m][k] < C[index][k]) {
                                    C[index][k] = C[prevIndex][m] + dur[m][k];
                                    parent[index][k] = m;
                                }
                            }
                        }
                    }
                }
                index = nextSetOf(s);
            }
        }
        for (var i = 0; i < numActive; ++i) {
            bestPath[i] = 0;
        }
        var index = (1 << numActive) - 1;
        if (mode == 0) {
            var currNode = -1;
            bestPath[numActive] = 0;
            for (var i = 1; i < numActive; ++i) {
                if (C[index][i] + dur[i][0] < bestTrip) {
                    bestTrip = C[index][i] + dur[i][0];
                    currNode = i;
                }
            }
            bestPath[numActive - 1] = currNode;
        } else {
            var currNode = numActive - 1;
            bestPath[numActive - 1] = numActive - 1;
            bestTrip = C[index][numActive - 1];
        }
        for (var i = numActive - 1; i > 0; --i) {
            currNode = parent[index][currNode];
            index -= (1 << bestPath[i]);
            bestPath[i - 1] = currNode;
        }
    }

    function makeLatLng(latLng) {
        return (latLng.toString().substr(1, latLng.toString().length - 2));
    }

    function makeDirWp(latLng, address) {
        if (address != null && address != "")
            return ({
                location: address,
                stopover: true
            });
        return ({
            location: latLng,
            stopover: true
        });
    }

    function getWayArr(curr) {
        var nextAbove = -1;
        for (var i = curr + 1; i < waypoints.length; ++i) {
            if (wpActive[i]) {
                if (nextAbove == -1) {
                    nextAbove = i;
                } else {
                    wayArr.push(makeDirWp(waypoints[i], addresses[i]));
                    wayArr.push(makeDirWp(waypoints[curr], addresses[curr]));
                }
            }
        }
        if (nextAbove != -1) {
            wayArr.push(makeDirWp(waypoints[nextAbove], addresses[nextAbove]));
            getWayArr(nextAbove);
            wayArr.push(makeDirWp(waypoints[curr], addresses[curr]));
        }
    }

    function getDistTable(curr, currInd) {
        var nextAbove = -1;
        var index = currInd;
        for (var i = curr + 1; i < waypoints.length; ++i) {
            if (wpActive[i]) {
                index++;
                if (nextAbove == -1) {
                    nextAbove = i;
                } else {
                    legs[currInd][index] = legsTmp[distIndex];
                    dist[currInd][index] = distances[distIndex];
                    dur[currInd][index] = durations[distIndex++];
                    legs[index][currInd] = legsTmp[distIndex];
                    dist[index][currInd] = distances[distIndex];
                    dur[index][currInd] = durations[distIndex++];
                }
            }
        }
        if (nextAbove != -1) {
            legs[currInd][currInd + 1] = legsTmp[distIndex];
            dist[currInd][currInd + 1] = distances[distIndex];
            dur[currInd][currInd + 1] = durations[distIndex++];
            getDistTable(nextAbove, currInd + 1);
            legs[currInd + 1][currInd] = legsTmp[distIndex];
            dist[currInd + 1][currInd] = distances[distIndex];
            dur[currInd + 1][currInd] = durations[distIndex++];
        }
    }

    function directions(mode) {
        if (cachedDirections) {
            // Bypass Google directions lookup if we already have the distance
            // and duration matrices.
            doTsp(mode);
        }
        wayArr = new Array();
        numActive = 0;
        numDirectionsComputed = 0;
        for (var i = 0; i < waypoints.length; ++i) {
            if (wpActive[i])++numActive;
        }
        numDirectionsNeeded = numActive * (numActive - 1);

        for (var i = 0; i < waypoints.length; ++i) {
            if (wpActive[i]) {
                wayArr.push(makeDirWp(waypoints[i], addresses[i]));
                getWayArr(i);
                break;
            }
        }

        // Roundtrip
        if (numActive > maxTspSize) {
            alert("Too many locations! You have " + numActive + ", but max limit is " + maxTspSize);
        } else {
            legsTmp = new Array();
            distances = new Array();
            durations = new Array();
            chunkNode = 0;
            okChunkNode = 0;
            if (typeof onProgressCallback == 'function') {
                onProgressCallback(tsp);
            }
            nextChunk(mode);
        }
    }

    function nextChunk(mode) {
        var percentage = ((okChunkNode / wayArr.length) * 100);
        if(Number(percentage.toFixed(1)) > Number(currentPercentage.toFixed(1))) {
            percentage = percentage > 100 ? 100 : percentage;
            logger.info(percentage.toFixed(1) + '%');
            currentPercentage = percentage;
        }
        chunkNode = okChunkNode;
        if (chunkNode < wayArr.length) {
            var wayArrChunk = new Array();
            for (var i = 0; i < maxSize && i + chunkNode < wayArr.length; ++i) {
                wayArrChunk.push(wayArr[chunkNode + i]);
            }
            var origin;
            var destination;
            origin = wayArrChunk[0].location;
            destination = wayArrChunk[wayArrChunk.length - 1].location;
            var wayArrChunk2 = new Array();
            for (var i = 1; i < wayArrChunk.length - 1; i++) {
                wayArrChunk2[i - 1] = wayArrChunk[i];
            }
            chunkNode += maxSize;
            if (chunkNode < wayArr.length - 1) {
                chunkNode--;
            }

            var myGebDirections = new google.maps.DirectionsService();

            myGebDirections.route({
                    origin: origin,
                    destination: destination,
                    waypoints: wayArrChunk2,
                    avoidHighways: avoidHighways,
                    avoidTolls: avoidTolls,
                    unitSystem: directionunits,
                    travelMode: travelMode
                },
                function(directionsResult, directionsStatus) {
                    console.log(' --- Directions Service Route Calculated');
                    console.log(' --- Total Requests ' + (++totalRequests));
                    if (directionsStatus == google.maps.DirectionsStatus.OK) {
                        requestLimitWait = 1000;
                        //alert("Request completed!");
                        // Save legs, distances and durations
                        fakeDirResult = directionsResult;
                        for (var i = 0; i < directionsResult.routes[0].legs.length; ++i) {
                            ++numDirectionsComputed;
                            legsTmp.push(directionsResult.routes[0].legs[i]);
                            durations.push(directionsResult.routes[0].legs[i].duration.value);
                            distances.push(directionsResult.routes[0].legs[i].distance.value);
                        }
                        if (typeof onProgressCallback == 'function') {
                            onProgressCallback(tsp);
                        }
                        okChunkNode = chunkNode;
                        nextChunk(mode);
                    } else if (directionsStatus === google.maps.DirectionsStatus.OVER_QUERY_LIMIT) {
                        // requestLimitWait *= 2;
                        console.log('Waiting ' + (requestLimitWait / 1000.0) + ' Second(s)...');
                        setTimeout(function() {
                            nextChunk(mode)
                        }, requestLimitWait);
                    } else {
                        var errorMsg = DIR_STATUS_MSG[directionsStatus];
                        var doNotContinue = true;
                        alert("Request failed: " + errorMsg);
                    }
                });
        } else {
            readyTsp(mode);
        }
    }

    function readyTsp(mode) {
        // Get distances and durations into 2-d arrays:
        distIndex = 0;
        legs = new Array();
        dist = new Array();
        dur = new Array();
        numActive = 0;
        for (var i = 0; i < waypoints.length; ++i) {
            if (wpActive[i]) {
                legs.push(new Array());
                dist.push(new Array());
                dur.push(new Array());
                addr[numActive] = addresses[i];
                numActive++;
            }
        }
        for (var i = 0; i < numActive; ++i) {
            legs[i][i] = null;
            dist[i][i] = 0;
            dur[i][i] = 0;
        }
        for (var i = 0; i < waypoints.length; ++i) {
            if (wpActive[i]) {
                getDistTable(i, 0);
                break;
            }
        }

        doTsp(mode);
    }

    function doTsp(mode) {
        //alert("doTsp");
        // Calculate shortest roundtrip:
        visited = new Array();
        for (var i = 0; i < numActive; ++i) {
            visited[i] = false;
        }
        currPath = new Array();
        bestPath = new Array();
        nextSet = new Array();
        bestTrip = maxTripSentry;
        visited[0] = true;
        currPath[0] = 0;
        cachedDirections = true;
        if (numActive <= maxTspBF + mode) {
            tspBruteForce(mode, 0, 0, 1);
        } else if (numActive <= maxTspDynamic + mode) {
            tspDynamic(mode);
        } else {
            tspAntColonyK2(mode);
            tspK3(mode);
        }

        prepareSolution();
    }

    function prepareSolution() {
        var wpIndices = new Array();
        for (var i = 0; i < waypoints.length; ++i) {
            if (wpActive[i]) {
                wpIndices.push(i);
            }
        }
        var bestPathLatLngStr = "";
        var directionsResultLegs = new Array();
        var directionsResultRoutes = new Array();
        var directionsResultOverview = new Array();
        var directionsResultBounds = new google.maps.LatLngBounds();
        for (var i = 1; i < bestPath.length; ++i) {
            directionsResultLegs.push(legs[bestPath[i - 1]][bestPath[i]]);
        }
        for (var i = 0; i < bestPath.length; ++i) {
            bestPathLatLngStr += makeLatLng(waypoints[wpIndices[bestPath[i]]]) + "\n";
            directionsResultBounds.extend(waypoints[wpIndices[bestPath[i]]]);
            directionsResultOverview.push(waypoints[wpIndices[bestPath[i]]]);
        }
        directionsResultRoutes.push({
            legs: directionsResultLegs,
            bounds: directionsResultBounds,
            copyrights: "Map data ©2012 Google",
            overview_path: directionsResultOverview,
            warnings: new Array(),
        });
        gebDirectionsResult = fakeDirResult;
        gebDirectionsResult.routes = directionsResultRoutes;

        if (onFatalErrorListener)
            google.maps.event.removeListener(onFatalErrorListener);
        onFatalErrorListener = google.maps.event.addListener(gebDirectionsService, 'error', onFatalErrorCallback);

        if (typeof onSolveCallback == 'function') {
            onSolveCallback(tsp);
        }
    }

    function reverseSolution() {
        for (var i = 0; i < bestPath.length / 2; ++i) {
            var tmp = bestPath[bestPath.length - 1 - i];
            bestPath[bestPath.length - 1 - i] = bestPath[i];
            bestPath[i] = tmp;
        }
        prepareSolution();
    }

    function reorderSolution(newOrder) {
        var newBestPath = new Array(bestPath.length);
        for (var i = 0; i < bestPath.length; ++i) {
            newBestPath[i] = bestPath[newOrder[i]];
        }
        bestPath = newBestPath;
        prepareSolution();
    }

    function removeStop(number) {
        var newBestPath = new Array(bestPath.length - 1);
        for (var i = 0; i < bestPath.length; ++i) {
            if (i != number) {
                newBestPath[i - (i > number ? 1 : 0)] = bestPath[i];
            }
        }
        bestPath = newBestPath;
        prepareSolution();
    }

    function addWaypoint(latLng, label) {
        var freeInd = -1;
        for (var i = 0; i < waypoints.length; ++i) {
            if (!wpActive[i]) {
                freeInd = i;
                break;
            }
        }
        if (freeInd == -1) {
            if (waypoints.length < maxTspSize) {
                waypoints.push(latLng);
                labels.push(label);
                wpActive.push(true);
                freeInd = waypoints.length - 1;
            } else {
                return (-1);
            }
        } else {
            waypoints[freeInd] = latLng;
            labels[freeInd] = label;
            wpActive[freeInd] = true;
        }
        return (freeInd);
    }

    function addAddress(address, label, callback) {
        addressProcessing = true;
        gebGeocoder.geocode({
            address: address
        }, function(results, status) {
            if (status == google.maps.GeocoderStatus.OK) {
                addressProcessing = false;
                --addressRequests;
                ++currQueueNum;
                if (results.length >= 1) {
                    var latLng = results[0].geometry.location;
                    var freeInd = addWaypoint(latLng, label);
                    address = address.replace("'", "");
                    address = address.replace("\"", "");
                    addresses[freeInd] = address;
                    if (typeof callback == 'function')
                        callback(address, latLng);
                }
            } else if (status == google.maps.GeocoderStatus.OVER_QUERY_LIMIT) {
                setTimeout(function() {
                    addAddress(address, label, callback)
                }, 100);
            } else {
                --addressRequests;
                alert("Failed to geocode address: " + address + ". Reason: " + GEO_STATUS_MSG[status]);
                ++currQueueNum;
                addressProcessing = false;
                if (typeof(callback) == 'function')
                    callback(address);
            }
        });
    }

    function swapWaypoints(i, j) {
        var tmpAddr = addresses[j];
        var tmpWaypoint = waypoints[j];
        var tmpActive = wpActive[j];
        var tmpLabel = labels[j];
        addresses[j] = addresses[i];
        addresses[i] = tmpAddr;
        waypoints[j] = waypoints[i];
        waypoints[i] = tmpWaypoint;
        wpActive[j] = wpActive[i];
        wpActive[i] = tmpActive;
        labels[j] = labels[i];
        labels[i] = tmpLabel;
    }

    BpTspSolver.prototype.startOver = function() {
        waypoints = new Array();
        addresses = new Array();
        labels = new Array();
        addr = new Array();
        wpActive = new Array();
        wayArr = new Array();
        legsTmp = new Array();
        distances = new Array();
        durations = new Array();
        legs = new Array();
        dist = new Array();
        dur = new Array();
        visited = new Array();
        currPath = new Array();
        bestPath = new Array();
        bestTrip = new Array();
        nextSet = new Array();
        travelMode = google.maps.DirectionsTravelMode.DRIVING;
        numActive = 0;
        chunkNode = 0;
        okChunkNode = 0;
        addressRequests = 0;
        addressProcessing = false;
        requestNum = 0;
        currQueueNum = 0;
        cachedDirections = false;
        onSolveCallback = function() {};
        onProgressCallback = null;
        doNotContinue = false;
        directionunits = google.maps.UnitSystem.METRIC;
        GEO_STATUS_MSG[google.maps.GeocoderStatus.OK] = "Success.";
        GEO_STATUS_MSG[google.maps.GeocoderStatus.INVALID_REQUEST] = "Request was invalid.";
        GEO_STATUS_MSG[google.maps.GeocoderStatus.ERROR] = "There was a problem contacting the Google servers.";
        GEO_STATUS_MSG[google.maps.GeocoderStatus.OVER_QUERY_LIMIT] = "The webpage has gone over the requests limit in too short a period of time.";
        GEO_STATUS_MSG[google.maps.GeocoderStatus.REQUEST_DENIED] = "The webpage is not allowed to use the geocoder.";
        GEO_STATUS_MSG[google.maps.GeocoderStatus.UNKNOWN_ERROR] = "A geocoding request could not be processed due to a server error. The request may succeed if you try again.";
        GEO_STATUS_MSG[google.maps.GeocoderStatus.ZERO_RESULTS] = "No result was found for this GeocoderRequest.";
        DIR_STATUS_MSG[google.maps.DirectionsStatus.INVALID_REQUEST] = "The DirectionsRequest provided was invalid.";
        DIR_STATUS_MSG[google.maps.DirectionsStatus.MAX_WAYPOINTS_EXCEEDED] = "Too many DirectionsWaypoints were provided in the DirectionsRequest. The total allowed waypoints is 8, plus the origin and destination.";
        DIR_STATUS_MSG[google.maps.DirectionsStatus.NOT_FOUND] = "At least one of the origin, destination, or waypoints could not be geocoded.";
        DIR_STATUS_MSG[google.maps.DirectionsStatus.OK] = "The response contains a valid DirectionsResult.";
        DIR_STATUS_MSG[google.maps.DirectionsStatus.OVER_QUERY_LIMIT] = "The webpage has gone over the requests limit in too short a period of time.";
        DIR_STATUS_MSG[google.maps.DirectionsStatus.REQUEST_DENIED] = "The webpage is not allowed to use the directions service.";
        DIR_STATUS_MSG[google.maps.DirectionsStatus.UNKNOWN_ERROR] = "A directions request could not be processed due to a server error. The request may succeed if you try again.";
        DIR_STATUS_MSG[google.maps.DirectionsStatus.ZERO_RESULTS] = "No route could be found between the origin and destination.";
    }

    /* end (edited) OptiMap code */
    /* start public interface */

    function BpTspSolver(map, panel, onFatalError) {
        if (tsp) {
            alert('You can only create one BpTspSolver at a time.');
            return;
        }

        gebMap = map;
        directionsPanel = panel;
        gebGeocoder = new google.maps.Geocoder();
        gebDirectionsService = new google.maps.DirectionsService();
        onFatalErrorCallback = onFatalError; // only for fatal errors, not geocoding errors
        tsp = this;
    }

    BpTspSolver.prototype.addAddressWithLabel = function(address, label, callback) {
        ++addressRequests;
        ++requestNum;
        tsp.addAddressAgain(address, label, callback, requestNum - 1);
    }

    BpTspSolver.prototype.addAddress = function(address, callback) {
        tsp.addAddressWithLabel(address, null, callback);
    };

    BpTspSolver.prototype.addAddressAgain = function(address, label, callback, queueNum) {
        if (addressProcessing || queueNum > currQueueNum) {
            setTimeout(function() {
                tsp.addAddressAgain(address, label, callback, queueNum)
            }, 100);
            return;
        }
        addAddress(address, label, callback);
    };

    BpTspSolver.prototype.addWaypointWithLabel = function(latLng, label, callback) {
        ++requestNum;
        tsp.addWaypointAgain(latLng, label, callback, requestNum - 1);
    };

    BpTspSolver.prototype.addWaypoint = function(latLng, callback) {
        tsp.addWaypointWithLabel(latLng, null, callback);
    };

    BpTspSolver.prototype.addWaypoints = function(arr) {
        arr.forEach(function(obj) {
          tsp.addWaypoint(obj);
        });
    };

    BpTspSolver.prototype.addWaypointAgain = function(latLng, label, callback, queueNum) {
        if (addressProcessing || queueNum > currQueueNum) {
            setTimeout(function() {
                tsp.addWaypointAgain(latLng, label, callback, queueNum)
            }, 100);
            return;
        }
        addWaypoint(latLng, label);
        ++currQueueNum;
        if (typeof(callback) == 'function') {
            callback(latLng);
        }
    }

    BpTspSolver.prototype.getWaypoints = function() {
        var wp = [];
        for (var i = 0; i < waypoints.length; i++) {
            if (wpActive[i]) {
                wp.push(waypoints[i]);
            }
        }
        return wp;
    };

    BpTspSolver.prototype.getAddresses = function() {
        var addrs = [];
        for (var i = 0; i < addresses.length; i++) {
            if (wpActive[i])
                addrs.push(addresses[i]);
        }
        return addrs;
    };

    BpTspSolver.prototype.getLabels = function() {
        var labs = [];
        for (var i = 0; i < labels.length; i++) {
            if (wpActive[i])
                labs.push(labels[i]);
        }
        return labs;
    };

    BpTspSolver.prototype.removeWaypoint = function(latLng) {
        for (var i = 0; i < waypoints.length; ++i) {
            if (wpActive[i] && waypoints[i].equals(latLng)) {
                wpActive[i] = false;
                return true;
            }
        }
        return false;
    };

    BpTspSolver.prototype.removeWaypoints = function() {
        for (var i = 0; i < waypoints.length; ++i) {
            wpActive[i] = false;
        }
    };

    BpTspSolver.prototype.removeAddress = function(addr) {
        for (var i = 0; i < addresses.length; ++i) {
            if (wpActive[i] && addresses[i] == addr) {
                wpActive[i] = false;
                return true;
            }
        }
        return false;
    };

    BpTspSolver.prototype.setAsStop = function(latLng) {
        var j = -1;
        for (var i = waypoints.length - 1; i >= 0; --i) {
            if (j == -1 && wpActive[i]) {
                j = i;
            }
            if (wpActive[i] && waypoints[i].equals(latLng)) {
                for (var k = i; k < j; ++k) {
                    swapWaypoints(k, k + 1);
                }
                break;
            }
        }
    }

    BpTspSolver.prototype.setAsStart = function(latLng) {
        var j = -1;
        for (var i = 0; i < waypoints.length; ++i) {
            if (j == -1 && wpActive[i]) {
                j = i;
            }
            if (wpActive[i] && waypoints[i].equals(latLng)) {
                for (var k = i; k > j; --k) {
                    swapWaypoints(k, k - 1);
                }
                break;
            }
        }
    }

    BpTspSolver.prototype.getGDirections = function() {
        return gebDirectionsResult;
    };

    BpTspSolver.prototype.renderDirections = function(map) {
        logger.info(' ');
        logger.info('Rendering directions');
        this.renderer = new google.maps.DirectionsRenderer();
        this.renderer.setMap(map);
        this.renderer.setDirections(tsp.getGDirections());
    };

    BpTspSolver.prototype.clearDirections = function() {
      if(this.renderer) {
        this.renderer.setMap(null);
      }
    };  

    BpTspSolver.prototype.getGDirectionsService = function() {
        return gebDirectionsService;
    };

    // Returns the order that the input locations was visited in.
    //   getOrder()[0] is always the starting location.
    //   getOrder()[1] gives the first location visited, getOrder()[2]
    //   gives the second location visited and so on.
    BpTspSolver.prototype.getOrder = function() {
        return bestPath;
    }

    // Methods affecting the way driving directions are computed
    BpTspSolver.prototype.getAvoidHighways = function() {
        return avoidHighways;
    }

    BpTspSolver.prototype.setAvoidHighways = function(avoid) {
        avoidHighways = avoid;
    }

    BpTspSolver.prototype.getAvoidTolls = function() {
        return avoidTolls;
    }

    BpTspSolver.prototype.setAvoidTolls = function(avoid) {
        avoidTolls = avoid;
    }

    BpTspSolver.prototype.getTravelMode = function() {
        return travelMode;
    }

    BpTspSolver.prototype.setTravelMode = function(travelM) {
        travelMode = travelM;
    }

    BpTspSolver.prototype.getDurations = function() {
        return dur;
    }

    // Helper functions
    BpTspSolver.prototype.getTotalDuration = function() {
        return gebDirections.getDuration().seconds;
    }

    // we assume that we have enough waypoints
    BpTspSolver.prototype.isReady = function() {
        return addressRequests == 0;
    };

    BpTspSolver.prototype.solveRoundTrip = function(callback) {
        if (doNotContinue) {
            alert('Cannot continue after fatal errors.');
            return;
        }

        if (!this.isReady()) {
            setTimeout(function() {
                tsp.solveRoundTrip(callback)
            }, 20);
            return;
        }
        if (typeof callback == 'function')
            onSolveCallback = callback;

        directions(0);
        totalRequests = 0;
        currentPercentage = 0;
    };

    BpTspSolver.prototype.solveAtoZ = function(callback) {
        if (doNotContinue) {
            alert('Cannot continue after fatal errors.');
            return;
        }

        if (!this.isReady()) {
            setTimeout(function() {
                tsp.solveAtoZ(callback)
            }, 20);
            return;
        }

        if (typeof callback == 'function')
            onSolveCallback = callback;

        directions(1);
    };

    BpTspSolver.prototype.setDirectionUnits = function(mOrKm) {
        if (mOrKm == "m") {
            directionunits = google.maps.UnitSystem.IMPERIAL;
        } else {
            directionunits = google.maps.UnitSystem.METRIC;
        }
    }

    BpTspSolver.prototype.setOnProgressCallback = function(callback) {
        onProgressCallback = callback;
    }

    BpTspSolver.prototype.getNumDirectionsComputed = function() {
        return numDirectionsComputed;
    }

    BpTspSolver.prototype.getNumDirectionsNeeded = function() {
        return numDirectionsNeeded;
    }

    BpTspSolver.prototype.reverseSolution = function() {
        reverseSolution();
    }

    BpTspSolver.prototype.reorderSolution = function(newOrder, callback) {
        if (typeof callback == 'function')
            onSolveCallback = callback;

        reorderSolution(newOrder);
    }

    BpTspSolver.prototype.removeStop = function(number, callback) {
        if (typeof callback == 'function')
            onSolveCallback = callback;

        removeStop(number);
    }

    window.BpTspSolver = BpTspSolver;
    module.exports = BpTspSolver;
})(
    require('../js/logger.js')
);

},{"../js/logger.js":4}],2:[function(require,module,exports){
/*
  These are the implementation-specific parts of the OptiMap application at
  http://www.gebweb.net/optimap

  This should serve as an example on how to use the more general BpTspSolver.js
  from http://code.google.com/p/google-maps-tsp-solver/

  Author: Geir K. Engdahl
*/

var tsp; // The BpTspSolver object which handles the TSP computation.
var mode;
var markers = new Array();  // Need pointers to all markers to clean up.
var dirRenderer;  // Need pointer to path to clean up.

/* Returns a textual representation of time in the format 
 * "N days M hrs P min Q sec". Does not include days if
 * 0 days etc. Does not include seconds if time is more than
 * 1 hour.
 */
function formatTime(seconds) {
    var days;
    var hours;
    var minutes;
    days = parseInt(seconds / (24*3600));
    seconds -= days * 24 * 3600;
    hours = parseInt(seconds / 3600);
    seconds -= hours * 3600;
    minutes = parseInt(seconds / 60);
    seconds -= minutes * 60;
    var ret = "";
    if (days > 0) 
	ret += days + " days ";
    if (days > 0 || hours > 0) 
	ret += hours + " hrs ";
    if (days > 0 || hours > 0 || minutes > 0) 
	ret += minutes + " min ";
    if (days == 0 && hours == 0)
	ret += seconds + " sec";
    return(ret);
}

/* Returns textual representation of distance in the format
 * "N km M m". Does not include km if less than 1 km. Does not
 * include meters if km >= 10.
 */
function formatLength(meters) {
    var km = parseInt(meters / 1000);
    meters -= km * 1000;
    var ret = "";
    if (km > 0) 
	ret += km + " km ";
    if (km < 10)
	ret += meters + " m";
    return(ret);
}

/* Returns textual representation of distance in the format
 * "N.M miles".
 */
function formatLengthMiles(meters) {
  var sMeters = meters * 0.621371192;
  var miles = parseInt(sMeters / 1000);
  var commaMiles = parseInt((sMeters - miles * 1000 + 50) / 100);
  var ret = miles + "." + commaMiles + " miles";
  return(ret);
}

/* Returns two HTML strings representing the driving directions.
 * Icons match the ones shown in the map. Addresses are used
 * as headers where available.
 * First string is suitable for use in reordering the directions.
 * Second string is suitable for printed directions.
 */
function formatDirections(gdir, mode) {
    var addr = tsp.getAddresses();
    var labels = tsp.getLabels();
    var order = tsp.getOrder();
    var retStr = "<table class='gebddir' border=0 cell-spacing=0>\n";
    var dragStr = "Drag to re-order stops:<br><ul class='unsortable'>";
    var retArr = new Array();
    for (var i = 0; i < gdir.legs.length; ++i) {
	var route = gdir.legs[i];
	var colour = "g";
	var number = i+1;
	retStr += "\t<tr class='heading'><td class='heading' width=40>"
	    + "<div class='centered-directions'><img src='iconsnew/black"
	    + number + ".png'></div></td>"
	    + "<td class='heading'><div class='centered-directions'>";
	var headerStr;
	if (labels[order[i]] != null && labels[order[i]] != "") {
	    headerStr = labels[order[i]];
	} else if (addr[order[i]] != null) {
	    headerStr = addr[order[i]];
	} else {
	    var prevI = (i == 0) ? gdir.legs.length - 1 : i-1;
	    var latLng = gdir.legs[prevI].end_location;
	    headerStr = gdir.legs[i].start_location.toString();
	}
	dragStr += "<li id='" + i + "' class='ui-state-"
	  + (i ? "default" : "disabled") + "'>"
	  + "<table class='dragTable'><tr><td class='left'><img src='iconsnew/black"
	  + number + ".png' /></td><td class='middle'>" + headerStr + "</td><td class='right'>"
	  + (i ? "<button id='dragClose" + i + "' value='" + i + "'></button>" : "")
	  + "</td></tr></table></li>"; 
	if (i == 0) {
	  dragStr += "</ul><ul id='sortable'>";
	}

	retStr += headerStr + "</div></td></tr>\n";
	for (var j = 0; j < route.steps.length; ++j) {
	    var classStr = "odd";
	    if (j % 2 == 0) classStr = "even";
	    retStr += "\t<tr class='text'><td class='" + classStr + "'></td>"
		+ "<td class='" + classStr + "'>"
		+ route.steps[j].instructions + "<div class='left-shift'>"
		+ route.steps[j].distance.text + "</div></td></tr>\n";
	}
    }
    dragStr += "</ul><ul class='unsortable'>";
    if (mode == 0) {
	var headerStr;
	if (labels[order[0]] != null && labels[order[0]] != "") {
	    headerStr = labels[order[0]];
	} else if (addr[order[0]] != null) {
	    headerStr = addr[order[0]];
	} else {
	    var prevI = gdir.legs.length - 1;
	    var latLng = gdir.legs[prevI].end_location;
	    headerStr = latLng.toString();
	}
	dragStr += "<li id='" + 0 + "' class='ui-state-disabled'>"
	  + "<table class='dragTable'><tr><td><img src='iconsnew/black"
	  + 1 + ".png' /></td><td>" + headerStr
	  + "</td></tr></table></li>"; 
	retStr += "\t<tr class='heading'><td class='heading'>"
	    + "<div class='centered-directions'><img src='iconsnew/black1.png'></div></td>"
	    + "<td class='heading'>"
	    + "<div class='centered-directions'>" 
	    + headerStr + "</div></td></tr>\n";
    } else if (mode == 1) {
	var headerStr;
	if (labels[order[gdir.legs.length]] != null && labels[order[gdir.legs.length]] != "") {
	    headerStr = labels[order[gdir.legs.length]];
	} else if (addr[order[gdir.legs.length]] == null) {
	    var latLng = gdir.legs[gdir.legs.length - 1].end_location;
	    headerStr = latLng.toString();
	} else {
	    headerStr = addr[order[gdir.legs.length]];
	}
	dragStr += "<li id='" + gdir.legs.length + "' class='ui-state-disabled'>"
	  + "<table class='dragTable'><tr><td><img src='iconsnew/black"
	  + (gdir.legs.length + 1) + ".png' /></td><td>"
	  + headerStr + "</td></tr></table></li>"; 
	retStr += "\t<tr class='heading'><td class='heading'>"
	    + "<div class='centered-directions'><img src='iconsnew/black"
	    + (gdir.legs.length + 1) + ".png'></div></td>"
	    + "<td class='heading'>"
	    + "<div class='centered-directions'>" 
	    + headerStr + "</div></td></tr>\n";
    }
    dragStr += "</ul>";
    retStr += "</table>";
    retArr[0] = dragStr;
    retArr[1] = retStr;
    return(retArr);
}

function createTomTomLink(gdir) {
    var addr = tsp.getAddresses();
    var labels = tsp.getLabels();
    var order = tsp.getOrder();
    var addr2 = new Array();
    var label2 = new Array();
    for (var i = 0; i < order.length; ++i) {
	addr2[i] = addr[order[i]];
	if (order[i] < labels.length && labels[order[i]] != null && labels[order[i]] != "")
	    label2[i] = labels[order[i]];
    }
    var itn = createTomTomItineraryItn(gdir, addr2, label2);
    var retStr = "<form method='GET' action='tomtom.php' target='tomTomIFrame'>\n";
    retStr += "<input type='hidden' name='itn' value='" + itn + "' />\n";
    retStr += "<input id='tomTomButton' class='calcButton' type='submit' value='Send to TomTom' onClick='jQuery(\"#dialogTomTom\").dialog(\"open\");'/>\n";
    retStr += "</form>\n";
    return retStr;
}

function createGarminLink(gdir) {
    var addr = tsp.getAddresses();
    var labels = tsp.getLabels();
    var order = tsp.getOrder();
    var addr2 = new Array();
    var label2 = new Array();
    for (var i = 0; i < order.length; ++i) {
	addr2[i] = addr[order[i]];
	if (order[i] < labels.length && labels[order[i]] != null && labels[order[i]] != "")
	    label2[i] = labels[order[i]];
    }
    var gpx = createGarminGpx(gdir, addr2, label2);
    var gpxWp = createGarminGpxWaypoints(gdir, addr2, label2);
    var retStr = "<form method='POST' action='garmin.php' target='garminIFrame'>\n";
    retStr += "<input type='hidden' name='gpx' value='" + gpx + "' />\n";
    retStr += "<input type='hidden' name='gpxWp' value='" + gpxWp + "' />\n";
    retStr += "<input id='garminButton' class='calcButton' type='submit' value='Send to Garmin' onClick='jQuery(\"#dialogGarmin\").dialog(\"open\");'/>\n";
    retStr += "</form>\n";
    return retStr;
}

function createGoogleLink(gdir) {
    var addr = tsp.getAddresses();
    var order = tsp.getOrder();
    var ret = "http://maps.google.com/maps?saddr=";
    for (var i = 0; i < order.length; ++i) {
	if (i == 1) {
	    ret += "&daddr=";
	} else if (i >= 2) {
	    ret += " to:";
	}
	if (addr[order[i]] != null && addr[order[i]] != "") {
	  ret += escape(addr[order[i]]);
	} else {
	    if (i == 0) {
		ret += gdir.legs[0].start_location.toString();
	    } else {
		ret += gdir.legs[i-1].end_location.toString();
	    }
	}
    }
    return ret;
}

function getWindowHeight() {
    if (typeof(window.innerHeight) == 'number')
	return window.innerHeight;
    if (document.documentElement && document.documentElement.clientHeight)
	return document.documentElement.clientHeight;
    if (document.body && document.body.clientHeight)
	return document.body.clientHeight;
    return 800;
}

function getWindowWidth() {
    if (typeof(window.innerWidth) == 'number')
	return window.innerWidth;
    if (document.documentElement && document.documentElement.clientWidth)
	return document.documentElement.clientWidth;
    if (document.body && document.body.clientWidth)
	return document.body.clientWidth;
    return 1200;
}

function onProgressCallback(tsp) {
  jQuery('#progressBar').progressbar('value', 100 * tsp.getNumDirectionsComputed() / tsp.getNumDirectionsNeeded());
}

function setMarkerAsStart(marker) {
    marker.infoWindow.close();
    tsp.setAsStart(marker.getPosition());
    drawMarkers(false);
}

function setMarkerAsStop(marker) {
    marker.infoWindow.close();
    tsp.setAsStop(marker.getPosition());
    drawMarkers(false);
}

function removeMarker(marker) {
    marker.infoWindow.close();
    tsp.removeWaypoint(marker.getPosition());
    drawMarkers(false);
}

function drawMarker(latlng, addr, label, num) {
    var icon;
    icon = new google.maps.MarkerImage("iconsnew/red" + (num + 1) + ".png");
    var marker = new google.maps.Marker({ 
        position: latlng, 
	icon: icon, 
	map: gebMap });
    google.maps.event.addListener(marker, 'click', function(event) {
	var addrStr = (addr == null) ? "" : addr + "<br>";
	var labelStr = (label == null) ? "" : "<b>" + label + "</b><br>";
	var markerInd = -1;
	for (var i = 0; i < markers.length; ++i) {
	    if (markers[i] != null && marker.getPosition().equals(markers[i].getPosition())) {
		markerInd = i;
		break;
	    }
	}
	var infoWindow = new google.maps.InfoWindow({ 
	    content: labelStr + addrStr
		+ "<a href='javascript:setMarkerAsStart(markers[" 
		+ markerInd + "]"
		+ ")'>"
		+ "Set as starting location"
		+ "</a><br>"
		+ "<a href='javascript:setMarkerAsStop(markers["
		+ markerInd + "])'>"
		+ "Set as ending location"
		+ "</a><br>"
		+ "<a href='javascript:removeMarker(markers["
		+ markerInd + "])'>"
		+ "Remove location</a>",
	    position: marker.getPosition() });
	marker.infoWindow = infoWindow;
	infoWindow.open(gebMap);
	//    tsp.removeWaypoint(marker.getPosition());
	//    marker.setMap(null);
    });
    markers.push(marker);
}

function setViewportToCover(waypoints) {
    var bounds = new google.maps.LatLngBounds();
    for (var i = 0; i < waypoints.length; ++i) {
	bounds.extend(waypoints[i]);
    }
    gebMap.fitBounds(bounds);
}

function initMap(center, zoom, div) {
    var myOptions = {
	zoom: zoom,
	center: center,
	mapTypeId: google.maps.MapTypeId.ROADMAP
    };
    gebMap = new google.maps.Map(div, myOptions);
    google.maps.event.addListener(gebMap, "click", function(event) {
	tsp.addWaypoint(event.latLng, addWaypointSuccessCallback);
    });
}

function loadAtStart(lat, lng, zoom) {
    var center = new google.maps.LatLng(lat, lng);
    initMap(center, zoom, document.getElementById("map"));
    directionsPanel = document.getElementById("my_textual_div");
    
    tsp = new BpTspSolver(gebMap, directionsPanel);
    google.maps.event.addListener(tsp.getGDirectionsService(), "error", function() {
	alert("Request failed: " + reasons[tsp.getGDirectionsService().getStatus().code]);
    });
}

function addWaypointWithLabel(latLng, label) {
    tsp.addWaypointWithLabel(latLng, label, addWaypointSuccessCallbackZoom);
}

function addWaypoint(latLng) {
    addWaypointWithLabel(latLng, null, addWaypointSuccessCallbackZoom);
}

function addAddressAndLabel(addr, label) {
    tsp.addAddressWithLabel(addr, label, addAddressSuccessCallbackZoom);
}

function addAddress(addr) {
    addAddressAndLabel(addr, null);
}

function clickedAddAddress() {
    addAddress(document.address.addressStr.value);
}

function addAddressSuccessCallback(address, latlng) {
    if (latlng) {
	drawMarkers(false);
    } else {
	alert('Failed to geocode: ' + address);
    }
}

function addAddressSuccessCallbackZoom(address, latlng) {
    if (latlng) {
	drawMarkers(true);
    } else {
	alert('Failed to geocode: ' + address);
    }
}

function addWaypointSuccessCallback(latlng) {
    if (latlng) {
	drawMarkers(false);
    }
}

function addWaypointSuccessCallbackZoom(latlng) {
    if (latlng) {
	drawMarkers(true);
    }
}

function drawMarkers(updateViewport) {
    removeOldMarkers();
    var waypoints = tsp.getWaypoints();
    var addresses = tsp.getAddresses();
    var labels = tsp.getLabels();
    for (var i = 0; i < waypoints.length; ++i) {
	drawMarker(waypoints[i], addresses[i], labels[i], i);
    }
    if (updateViewport) {
	setViewportToCover(waypoints);
    }
}

function startOver() {
    document.getElementById("my_textual_div").innerHTML = "";
    document.getElementById("path").innerHTML = "";
    var center = gebMap.getCenter();
    var zoom = gebMap.getZoom();
    var mapDiv = gebMap.getDiv();
    initMap(center, zoom, mapDiv);
    tsp.startOver(); // doesn't clearOverlays or clear the directionsPanel
}

function directions(m, walking, avoid) {
    jQuery('#dialogProgress').dialog('open');
    mode = m;
    tsp.setAvoidHighways(avoid);
    if (walking)
	tsp.setTravelMode(google.maps.DirectionsTravelMode.WALKING);
    else
	tsp.setTravelMode(google.maps.DirectionsTravelMode.DRIVING);
    tsp.setOnProgressCallback(onProgressCallback);
    if (m == 0)
	tsp.solveRoundTrip(onSolveCallback);
    else
	tsp.solveAtoZ(onSolveCallback);
}

function getTotalDuration(dir) {
    var sum = 0;
    for (var i = 0; i < dir.legs.length; i++) {
	sum += dir.legs[i].duration.value;
    }
    return sum;
}

function getTotalDistance(dir) {
    var sum = 0;
    for (var i = 0; i < dir.legs.length; i++) {
	sum += dir.legs[i].distance.value;
    }
    return sum;
}

function removeOldMarkers() {
    for (var i = 0; i < markers.length; ++i) {
	markers[i].setMap(null);
    }
    markers = new Array();
}

function onSolveCallback(myTsp) {
  jQuery('#dialogProgress').dialog('close');
    var dirRes = tsp.getGDirections();
    var dir = dirRes.routes[0];
    // Print shortest roundtrip data:
    
    var pathStr = "<p>Trip duration: " + formatTime(getTotalDuration(dir)) + "<br>";
    pathStr += "Trip length: " + formatLength(getTotalDistance(dir)) + 
      " (" + formatLengthMiles(getTotalDistance(dir)) + ")</p>";
    document.getElementById("path").innerHTML = pathStr;
    document.getElementById("exportDataButton").innerHTML = "<input id='rawButton' class='calcButton' type='button' value='Toggle raw path output' onClick='toggle(\"exportData\"); document.getElementById(\"outputList\").select();'>";
    var durStr = "<input id='csvButton' class='calcButton' type='button' value='Toggle csv durations matrix' onClick='toggle(\"durationsData\");'>";
    document.getElementById("durations").innerHTML = durStr;
    document.getElementById("exportLabelButton").innerHTML = "<input id='rawLabelButton' class='calcButton' type='button' value='Raw path with labels' onClick='toggle(\"exportLabelData\"); document.getElementById(\"outputLabelList\").select();'>"
    document.getElementById("exportAddrButton").innerHTML = "<input id='rawAddrButton' class='calcButton' type='button' value='Optimal address order' onClick='toggle(\"exportAddrData\"); document.getElementById(\"outputAddrList\").select();'>"
    document.getElementById("exportOrderButton").innerHTML = "<input id='rawOrderButton' class='calcButton' type='button' value='Optimal numeric order' onClick='toggle(\"exportOrderData\"); document.getElementById(\"outputOrderList\").select();'>"

    var formattedDirections = formatDirections(dir, mode);
    document.getElementById("routeDrag").innerHTML = formattedDirections[0];
    document.getElementById("my_textual_div").innerHTML = formattedDirections[1];
    document.getElementById("garmin").innerHTML = createGarminLink(dir);
    document.getElementById("tomtom").innerHTML = createTomTomLink(dir);
    document.getElementById("exportGoogle").innerHTML = "<input id='googleButton' value='View in Google Maps' type='button' class='calcButton' onClick='window.open(\"" + createGoogleLink(dir) + "\");' />";
    document.getElementById("reverseRoute").innerHTML = "<input id='reverseButton' value='Reverse' type='button' class='calcButton' onClick='reverseRoute()' />";
    jQuery('#reverseButton').button();
    jQuery('#rawButton').button();
    jQuery('#rawLabelButton').button();
    jQuery('#csvButton').button();
    jQuery('#googleButton').button();
    jQuery('#tomTomButton').button();
    jQuery('#garminButton').button();
    jQuery('#rawAddrButton').button();
    jQuery('#rawOrderButton').button();

    jQuery("#sortable").sortable({ stop: function(event, ui) {
	  var perm = jQuery("#sortable").sortable("toArray");
	  var numPerm = new Array(perm.length + 2);
	  numPerm[0] = 0;
	  for (var i = 0; i < perm.length; i++) {
	    numPerm[i + 1] = parseInt(perm[i]);
	  }
	  numPerm[numPerm.length - 1] = numPerm.length - 1;
	  tsp.reorderSolution(numPerm, onSolveCallback);
	} });
    jQuery("#sortable").disableSelection();
    for (var i = 1; i < dir.legs.length; ++i) {
      var finalI = i;
      jQuery("#dragClose" + i).button({
	icons: { primary: "ui-icon-close" },
	    text: false
	    }).click(function() {
		tsp.removeStop(parseInt(this.value), null);
	      });
    }
    removeOldMarkers();

    // Add nice, numbered icons.
    if (mode == 1) {
	var myPt1 = dir.legs[0].start_location;
	var myIcn1 = new google.maps.MarkerImage("iconsnew/black1.png");
	var marker = new google.maps.Marker({ 
            position: myPt1, 
	    icon: myIcn1, 
	    map: gebMap });
	markers.push(marker);
    }
    for (var i = 0; i < dir.legs.length; ++i) {
	var route = dir.legs[i];
	var myPt1 = route.end_location;
	var myIcn1;
	if (i == dir.legs.length - 1 && mode == 0) {
	    myIcn1 = new google.maps.MarkerImage("iconsnew/black1.png");
	} else {
	    myIcn1 = new google.maps.MarkerImage("iconsnew/black" + (i+2) + ".png");
	}
	var marker = new google.maps.Marker({
            position: myPt1,
	    icon: myIcn1,
	    map: gebMap });
	markers.push(marker);
    }
    // Clean up old path.
    if (dirRenderer != null) {
	dirRenderer.setMap(null);
    }
    dirRenderer = new google.maps.DirectionsRenderer({
	directions: dirRes,
	hideRouteList: true,
	map: gebMap,
	panel: null,
	preserveViewport: false,
	suppressInfoWindows: true,
	suppressMarkers: true });

    // Raw path output
    var bestPathLatLngStr = dir.legs[0].start_location.toString() + "\n";
    for (var i = 0; i < dir.legs.length; ++i) {
	bestPathLatLngStr += dir.legs[i].end_location.toString() + "\n";
    }
    document.getElementById("exportData_hidden").innerHTML = 
	"<textarea id='outputList' rows='10' cols='40'>" 
	+ bestPathLatLngStr + "</textarea><br>";

    // Raw path output with labels
    var labels = tsp.getLabels();
    var order = tsp.getOrder();
    var bestPathLabelStr = "";
    if (labels[order[0]] == null) {
      bestPathLabelStr += order[0];
    } else {
      bestPathLabelStr += labels[order[0]];
    }
    bestPathLabelStr += ": " + dir.legs[0].start_location.toString() + "\n";
    for (var i = 0; i < dir.legs.length; ++i) {
      if (labels[order[i+1]] == null) {
	bestPathLabelStr += order[i+1];
      } else {
	bestPathLabelStr += labels[order[i+1]];
      }
      bestPathLabelStr += ": " + dir.legs[i].end_location.toString() + "\n";
    }
    document.getElementById("exportLabelData_hidden").innerHTML = 
	"<textarea id='outputLabelList' rows='10' cols='40'>" 
      + bestPathLabelStr + "</textarea><br>";

    // Optimal address order
    var addrs = tsp.getAddresses();
    var order = tsp.getOrder();
    var bestPathAddrStr = "";
    if (addrs[order[0]] == null) {
      bestPathAddrStr += dir.legs[0].start_location.toString();
    } else {
      bestPathAddrStr += addrs[order[0]];
    }
    bestPathAddrStr += "\n";
    for (var i = 0; i < dir.legs.length; ++i) {
      if (addrs[order[i+1]] == null) {
	bestPathAddrStr += dir.legs[i].end_location.toString();
      } else {
	bestPathAddrStr += addrs[order[i+1]];
      }
      bestPathAddrStr += "\n";
    }
    document.getElementById("exportAddrData_hidden").innerHTML = 
	"<textarea id='outputAddrList' rows='10' cols='40'>" 
      + bestPathAddrStr + "</textarea><br>";

    // Optimal numeric order
    var bestOrderStr = "";
    for (var i = 0; i < order.length; ++i) {
      bestOrderStr += "" + (order[i] + 1) + "\n";
    }
    document.getElementById("exportOrderData_hidden").innerHTML =
        "<textarea id='outputOrderList' rows='10' cols='40'>" 
      + bestOrderStr + "</textarea><br>";

    var durationsMatrixStr = "";
    var dur = tsp.getDurations();
    for (var i = 0; i < dur.length; ++i) {
	for (var j = 0; j < dur[i].length; ++j) {
	    durationsMatrixStr += dur[i][j];
	    if (j == dur[i].length - 1) {
		durationsMatrixStr += "\n";
	    } else {
		durationsMatrixStr += ", ";
	    }
	}
    }
    document.getElementById("durationsData_hidden").innerHTML = 
	"<textarea name='csvDurationsMatrix' rows='10' cols='40'>" 
	+ durationsMatrixStr + "</textarea><br>";
}

function clickedAddList() {
  var val = document.listOfLocations.inputList.value;
  val = val.replace(/\t/g, ' ');
  document.listOfLocations.inputList.value = val;
  addList(val);
}

function addList(listStr) {
    var listArray = listStr.split("\n");
    for (var i = 0; i < listArray.length; ++i) {
	var listLine = listArray[i];
	if (listLine.match(/\(?\s*\-?\d+\s*,\s*\-?\d+/) ||
	    listLine.match(/\(?\s*\-?\d+\s*,\s*\-?\d*\.\d+/) ||
	    listLine.match(/\(?\s*\-?\d*\.\d+\s*,\s*\-?\d+/) ||
	    listLine.match(/\(?\s*\-?\d*\.\d+\s*,\s*\-?\d*\.\d+/)) {
	    // Line looks like lat, lng.
	    var cleanStr = listLine.replace(/[^\d.,-]/g, "");
	    var latLngArr = cleanStr.split(",");
	    if (latLngArr.length == 2) {
		var lat = parseFloat(latLngArr[0]);
		var lng = parseFloat(latLngArr[1]);
		var latLng = new google.maps.LatLng(lat, lng);
		tsp.addWaypoint(latLng, addWaypointSuccessCallbackZoom);
	    }
	} else if (listLine.match(/\(?\-?\d*\.\d+\s+\-?\d*\.\d+/)) {
	  // Line looks like lat lng
	    var latLngArr = listline.split(" ");
	    if (latLngArr.length == 2) {
		var lat = parseFloat(latLngArr[0]);
		var lng = parseFloat(latLngArr[1]);
		var latLng = new google.maps.LatLng(lat, lng);
		tsp.addWaypoint(latLng, addWaypointSuccessCallbackZoom);
	    }
	} else if (listLine.match(/\S+/)) {
	    // Non-empty line that does not look like lat, lng. Interpret as address.
	    tsp.addAddress(listLine, addAddressSuccessCallbackZoom);
	}
    }
}

function reverseRoute() {
    tsp.reverseSolution();
}

},{}],3:[function(require,module,exports){
(function(ui) {
	ui.init();
})(
	require('./ui.js')
);
},{"./ui.js":5}],4:[function(require,module,exports){
(function() {

	var logger = {

		info: function(message) {
			var textArea = logger.getTextArea();
			textArea.value += (message + '\n');
			textArea.scrollTop = textArea.scrollHeight;
		},

		getTextArea: function() {
			return document.getElementById('directions');
		}
	};

	module.exports = logger;
})();
},{}],5:[function(require,module,exports){
/*

Example CSV Coords
38.644808,-90.268627,38.645193,-90.301607,38.638908,-90.294633,38.633494,-90.303195,38.633711,-90.271760,38.636845,-90.286759,38.628782,-90.302015,38.637716,-90.293239,38.652614,-90.296737,38.629870,-90.252813,38.612154,-90.263871,38.618491,-90.245825,38.631499,-90.239710,38.636560,-90.234110

*/

(function(BpTspSolver, logger) {

	var ui = {

		map: null,
		tsp: null,

		init: function() {
			ui.map = new google.maps.Map(document.getElementById('map'), {
				zoom: 14,
				center: new google.maps.LatLng(38.637350, -90.245388),
				mapTypeId: google.maps.MapTypeId.ROADMAP
			});
			ui.tsp = new BpTspSolver(map);
			ui.tsp.setTravelMode(google.maps.DirectionsTravelMode.DRIVING);
			ui.addListeners();
		},

		addListeners: function() {
			document.getElementById('submit').addEventListener('click', ui.onSubmit);
		},

		onSubmit: function(event) {
			var csvArea = document.getElementById('directions'),
				loading = document.getElementById('loading'),
				directions = csvArea.value.split(','),
				length = directions.length;

			event.target.disabled = true;
			loading.style.display = 'inline';
			csvArea.disabled = true;
			csvArea.value = '';

			ui.tsp.clearDirections();
			ui.tsp.startOver();

			for(var i = 0; i < length; i+=2) {
				ui.tsp.addWaypoint(new google.maps.LatLng(directions[i+1], directions[i]));
			}

			logger.info('Solving Route For ' + directions.length / 2 + ' Points...');
			logger.info('');
			var start = new Date().getTime() / 1000;
			ui.tsp.solveRoundTrip(function() {
				var stop = new Date().getTime() / 1000;
				ui.tsp.renderDirections(ui.map);
				
				logger.info('Calculated in ' + (stop - start) + ' seconds');

				// reset form
				event.target.disabled = false;
				loading.style.display = 'none';
				csvArea.disabled = false;
				logger.info('');
				logger.info('Done!');
			});
		}
	};

	module.exports = ui;
})(
	require('../google-maps-tsp-solver-read-only/BpTspSolver.js'),
	require('./logger.js')
);

},{"../google-maps-tsp-solver-read-only/BpTspSolver.js":1,"./logger.js":4}]},{},[3,4,5,1,2]);
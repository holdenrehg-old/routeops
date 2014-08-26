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

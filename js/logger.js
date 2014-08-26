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
module.exports = function(grunt) {
  grunt.initConfig({
    pkg: grunt.file.readJSON('package.json'),

    // concat js together
    browserify: {
  		'app.js': [
  			'js/test.js',
  			'google-maps-tsp-solver-read-only/BpTspSolver.js'
  		]
    },

    // watch task for js file changes
    watch: {
      files: [ 
        'js/test.js',
        'google-maps-tsp-solver-read-only/BpTspSolver.js'
      ],
      tasks: [ 'browserify' ]
    }
  })

  grunt.loadNpmTasks('grunt-browserify')
  grunt.loadNpmTasks('grunt-contrib-watch');
}
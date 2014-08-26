module.exports = function(grunt) {
  grunt.initConfig({
    pkg: grunt.file.readJSON('package.json'),

    // concat js together
    browserify: {
  		'app.js': [
  			'js/*.js',
  			'google-maps-tsp-solver-read-only/*.js'
  		]
    },

    // watch task for js file changes
    watch: {
      files: [ 
        'js/*.js',
        'google-maps-tsp-solver-read-only/*.js'
      ],
      tasks: [ 'browserify' ]
    }
  })

  grunt.loadNpmTasks('grunt-browserify')
  grunt.loadNpmTasks('grunt-contrib-watch');
}
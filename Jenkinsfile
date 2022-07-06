pipeline {
    agent any

    environment {
        SBT_FLAGS = "-Dsbt.log.noformat=true"
    }

    stages {
        stage('Cleaning') {
            steps {
                echo 'Cleaning...'
                sh 'sbt ${SBT_FLAGS} clean'
            }
        }
        stage('Formatting') {
            steps {
                echo 'Formatting...'
                sh 'sbt ${SBT_FLAGS} format'
                sh '''
                  echo "Modified files through scalariform:"
                  git diff
                  test -z "$(git ls-files -m)"
                '''
            }
        }
        stage('Building') {
            steps {
                echo 'Building...'
                sh 'sbt ${SBT_FLAGS} compile'
            }
        }
        stage('Testing') {
            steps {
                echo 'Testing...'
                sh 'sbt ${SBT_FLAGS} test'
            }
        }
        stage('Documentation') {
            steps {
                echo 'Testing...'
                sh 'sbt ${SBT_FLAGS} doc unidoc'
            }
        }
        stage('User manual') {
            steps {
                echo 'Building user manual...'
                sh 'sbt ${SBT_FLAGS} evalUserManual'
                sh '''
                  echo "Modified files through evalUserManual:"
                  git diff
                  test -z "$(git ls-files -m)"
                '''

            }
        }
        stage('Packaging') {
            steps {
                echo 'Packaging...'
                sh 'sbt ${SBT_FLAGS} releaseDist'
            }
        }
    }
    post {
    failure {
      emailext (
          subject: "FAILED: Job '${env.JOB_NAME} [${env.BUILD_NUMBER}]'",
          body:
          """<p>FAILED: Job '${env.JOB_NAME} [${env.BUILD_NUMBER}]':</p>
             <p>Check console output at &QUOT;<a href='${env.BUILD_URL}'>${env.JOB_NAME} [${env.BUILD_NUMBER}]</a>&QUOT;</p>
             <p>Build log: \${BUILD_LOG}</p>
          """,
          recipientProviders: [developers(), requestor()],
          to: 'gapt-group@googlegroups.com'
        )
    }
  }
}

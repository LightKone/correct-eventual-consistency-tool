# Correct Eventual Consistency (CEC) Tool 

This tool helps programmers verify whether their distributed application design is safe.

# Usage
1. Install [Docker Compose](https://docs.docker.com/compose/install/)
2. Download and extract the contents of the zip file.
3. `cd CEC`
4. `docker-compose run cec specifications/library specifications/applications/<application_name>.spec -c [specifications/restrictions/<restrictions_name>.json]`

Note : The application, library and restrictions directory must be inside the folder CEC.

# Writing specifications
## General guide on writing specifications
https://goncalobfm.github.io/docs/specifications/
## Writing reusable components
https://goncalobfm.github.io/docs/libraries/

# Checks performed by the tool
https://goncalobfm.github.io/docs/output/

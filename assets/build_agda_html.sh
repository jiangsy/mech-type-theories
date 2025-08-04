#!/bin/sh
SCRIPT_DIR=$(pwd)
ROOT_DIR=$SCRIPT_DIR/..

build_agda_html() {
    local proof_dir=$1
    
    echo "Building HTML for $proof_dir..."
    
    # Generate Agda HTML
    cd $SCRIPT_DIR/$proof_dir && agda --html --html-dir=$SCRIPT_DIR/src_htmls/$proof_dir --html-highlight=code README.agda
    
    # Setup and build HTML generator
    # Remove existing agda directory if it exists to avoid moving source inside it
    rm -rf $SCRIPT_DIR/html_generator/src/agda
    mv $SCRIPT_DIR/src_htmls/$proof_dir $SCRIPT_DIR/html_generator/src/agda
    mkdir -p $SCRIPT_DIR/html_generator/src/_data
    AGDA_PRJ_ROOT=README envsubst < $SCRIPT_DIR/html_generator/templates/src/_data/agdaModules.js > $SCRIPT_DIR/html_generator/src/_data/agdaModules.js
    cp $SCRIPT_DIR/html_generator/templates/src/agda/agda.11tydata.js $SCRIPT_DIR/html_generator/src/agda/
    
    # Build and cleanup
    cd $SCRIPT_DIR/html_generator && npm install && npm run build
    rm $SCRIPT_DIR/html_generator/src/_data/agdaModules.js
    rm -rf $SCRIPT_DIR/html_generator/src/agda
    
    # Remove existing html directory if it exists to avoid moving source inside it
    rm -rf $SCRIPT_DIR/$proof_dir/html
    mv $SCRIPT_DIR/html_generator/_site/agda $ROOT_DIR/html
    
    echo "Completed building HTML for $proof_dir"
}

# Clean up and prepare
rm -rf $SCRIPT_DIR/src_htmls && mkdir -p $SCRIPT_DIR/src_htmls

# Build HTML for all proof directories
build_agda_html "../src"

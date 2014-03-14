// An example Backbone application contributed by
// [Jérôme Gravel-Niquet](http://jgn.me/). This demo uses a simple
// [LocalStorage adapter](backbone-localstorage.html)
// to persist Backbone models within your browser.

// Load the application once the DOM is ready, using `jQuery.ready`:
$(function(){

  // Todo Model
  // ----------

  // Our basic **Todo** model has `title`, `order`, and `done` attributes.
  var Todo = Backbone.Model.extend({

    // Default attributes for the todo item.
    defaults: function() {
      return {
    	 id: "_",
         name: "",
         range: "",
         meaning: "",
         order: Todos.nextOrder(),
      };
    },
  });

  // Todo Collection
  // ---------------

  // The collection of todos is backed by *localStorage* instead of a remote
  // server.
  var TodoList = Backbone.Collection.extend({

    // Reference to this collection's model.
    model: Todo,
    
    url: "/",

    // Save all of the todo items under the `"todos-backbone"` namespace.
    //localStorage: new Backbone.LocalStorage("todos-backbone"),

    // We keep the Todos in sequential order, despite being saved by unordered
    // GUID in the database. This generates the next order number for new items.
    nextOrder: function() {
      if (!this.length) return 1;
      return this.last().get('order') + 1;
    },

    // Todos are sorted by their original insertion order.
    comparator: 'order'

  });

  // Create our global collection of **Todos**.
  var Todos = new TodoList;

  // Todo Item View
  // --------------

  // The DOM element for a todo item...
  var TodoView = Backbone.View.extend({

    //... is a list tag.
    tagName:  "tr",

    // Cache the template function for a single item.
    template: _.template($('#item-template').html()),

    // The DOM events specific to an item.
    events: {
      "click a.destroy" : "clear",
      "click .view-name"  : "edit_name",
      "blur .view-name .edit" : "close_name",
      "click .view-range"  : "edit_range",
      "blur .view-range .edit" : "close_range",
      "click .view-meaning"  : "edit_meaning",
      "blur .view-meaning .edit" : "close_meaning"
    },

    // The TodoView listens for changes to its model, re-rendering. Since there's
    // a one-to-one correspondence between a **Todo** and a **TodoView** in this
    // app, we set a direct reference on the model for convenience.
    initialize: function() {
      this.listenTo(this.model, 'change', this.render);
      this.listenTo(this.model, 'destroy', this.remove);
    },

    // Re-render the titles of the todo item.
    render: function() {
      this.$el.html(this.template(this.model.toJSON()));
      this.input = this.$('.edit');
      return this;
    },

    // Switch this view into `"editing"` mode, displaying the input field.
    edit_name: function() {
      this.$el.addClass("editing-name");
      $(this.$el).find(".view-name input").focus();
    },

    // Close the `"editing"` mode, saving changes to the todo.
    close_name: function() {
      var value = $(this.$el).find(".view-name input").val();
      this.model.save({name: value});
      this.$el.removeClass("editing-name");
    },

    // Switch this view into `"editing"` mode, displaying the input field.
    edit_range: function() {
      this.$el.addClass("editing-range");
      $(this.$el).find(".view-range input").focus();
    },

    // Close the `"editing"` mode, saving changes to the todo.
    close_range: function() {
      var value = $(this.$el).find(".view-range input").val();
      this.model.save({range: value});
      this.$el.removeClass("editing-range");
    },

    // Switch this view into `"editing"` mode, displaying the input field.
    edit_meaning: function() {
      this.$el.addClass("editing-meaning");
      $(this.$el).find(".view-meaning input").focus();
    },

    // Close the `"editing"` mode, saving changes to the todo.
    close_meaning: function() {
      var value = $(this.$el).find(".view-meaning input").val();
      this.model.save({meaning: value});
      this.$el.removeClass("editing-meaning");
    },

    // Remove the item, destroy the model.
    clear: function() {
      this.model.destroy();
    }

  });

  // The Application
  // ---------------

  // Our overall **AppView** is the top-level piece of UI.
  var AppView = Backbone.View.extend({

    // Instead of generating a new element, bind to the existing skeleton of
    // the App already present in the HTML.
    el: $("#todoapp"),

    // Delegated events for creating new items, and clearing completed ones.
    events: {
      "click #new-meaning": "getMeaning",
      "click .add-btn"  : "addNewItem",
      "keypress #new-todo":  "createOnEnter",
    },

    // At initialization we bind to the relevant events on the `Todos`
    // collection, when items are added or changed. Kick things off by
    // loading any preexisting todos that might be saved in *localStorage*.
    initialize: function() {

      this.new_concept = this.$("#new-concept");
      this.new_range = this.$("#new-range");
      this.new_meaning = this.$("#new-meaning");

      this.listenTo(Todos, 'add', this.addOne);
      this.listenTo(Todos, 'reset', this.addAll);
      this.listenTo(Todos, 'all', this.render);

      this.footer = this.$('footer');
      this.main = $('#main');

      Todos.fetch();
    },
    
    // Re-rendering the App just means refreshing the statistics -- the rest
    // of the app doesn't change.
    render: function() {
        this.main.show();
    },

    // Add a single todo item to the list by creating a view for it, and
    // appending its element to the `<ul>`.
    addOne: function(todo) {
      var view = new TodoView({model: todo});
      this.$("#todo-list").append(view.render().el);
    },

    // Add all items in the **Todos** collection at once.
    addAll: function() {
      Todos.each(this.addOne, this);
    },

    // If you hit return in the main input field, create new **Todo** model,
    // persisting it to *localStorage*.
    createOnEnter: function(e) {
      if (e.keyCode != 13) return;
      if (!this.input.val()) return;

      Todos.create({title: this.input.val()});
      this.input.val('');
    },

    getMeaning: function() {
    	var workflow = new sally.StartSubTask();
    	var _this = this;
		workflow.workflowID = "Sally.browse_ontology";
		Communication.sendMessage(workflow, function(data) {
			$(_this.new_meaning).text(data.uri);
		});
    },

    addNewItem: function(e) {
      Todos.create({
         name: $(this.new_concept).val(),
         range: $(this.new_range).val(),
         meaning: $(this.new_meaning).text(),
      });
    },

  });

  // Finally, we kick things off by creating the **App**.
  var App = new AppView;
});
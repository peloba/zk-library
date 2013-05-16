import sbt._
import Keys._

object MyBuild extends Build {
	val zkSettings = Defaults.defaultSettings ++ Seq(
		organization := "de.peloba",
		name := "zk",
		version := "1.0",
		scalaVersion := "2.10.1",
		crossScalaVersions := Seq("2.9.3", "2.10.1"),
		libraryDependencies := Seq(
			"org.scalatest" %% "scalatest" % "1.9.1"
		)
	)

	lazy val zk = Project("zk", file("."), settings = zkSettings)
}
